-- Prove2me | Theorems.Thm_QNoiseStab_Supplement_theorem_6_6
-- name    : QNoiseStab.Supplement.theorem_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:23:16.763502+00:00
-- url     : https://prove2.me/theorems/ec77a06e-62da-4ff5-95e6-b5a25a513886
-- title:
--   Theorem 6.6 — matrix-vector product with a $(g,h,c)$-rigid matrix needs $T\ge C\,cnh/S$ queries (corrected: $0<c\le 1$)
-- statement:
--   There is a constant $C>0$ such that the following holds. Let $M$ be an $n\times n$ matrix over a field $F$ that is $(g,h,c)$-rigid with $0<c\le 1$, with $n$ sufficiently large, and let $D\subseteq F$ be finite with $|D|\ge2$. Every quantum algorithm with $T$ queries and space
--
--   $$
--   S<\min\Bigl(\frac{cg}{17},\ \frac{ch}{544}\Bigr)
--   $$
--
--   (intermediate measurements allowed, outputs committed during the run) that computes $f_M:D^n\to F^n$, $f_M(x)=Mx$ — commits all $n$ coordinates of $Mx$, all correctly — with success probability larger than $2^{-S}$ on a uniformly random input $x\in D^n$ satisfies
--
--   $$
--   T\ \ge\ C\,\frac{c\,n\,h}{S}.
--   $$
--
--   With the DFT matrix, which is $(n/4,n/4,1/2)$-rigid, this gives $T=\Omega(n^2/S)$ for the discrete Fourier transform, and it recovers the quantum lower bounds for convolution and integer multiplication.
--
--   Differences from the source:
--   - correction: M is (g, h, c)-rigid (Definition 6.1, c any real) → 0 < c and c ≤ 1 added; reason: the rank fraction c is implicitly in (0, 1] (rank of k rows is at most k; (g, h, 1)-rigid is the top case), and the literal statement is false outside it, e.g. for c = −1 and g = h = −N with N > 0, or for g = 1/2, c = K·S and h = K·n with K large, every matrix is vacuously (g, h, c)-rigid (no nonempty row set has |R| ≤ g), so M = 0 qualifies; f_0 = 0 is computed with success 1 by committing 0 to coordinate j at step j, using T = n − 1 queries and S = ⌈log₂ n⌉ + 1 qubits (S < min(cg/17, ch/544) holds), while the printed bound C·c·n·h/S (= C·N·n/S, resp. C·K²·n²) exceeds n − 1 once N or K is large
--   - generalization: §2.2 space-bounded circuits: unitaries U_t, flag and output measurements (fully general model of [HM23]) or fixed-time output measurements (output-oblivious model), reset measurements, start state |0⟩ → SpaceBoundedAlg: an arbitrary quantum instrument per step with outcome 'no output' or 'commit (j, v)', and an arbitrary input-independent start density matrix; reason: every §2.2 circuit (fully general or output-oblivious) composes into one instrument per step, so the Lean class contains the paper's and the statement specializes to it
--   - generalization: the algorithm uses S qubits of memory, its whole state stored in qubits → FitsInSpace S: n · d · |W| ≤ 2^S for the memory (Fin n × ZMod d) × W, query and phase registers included; reason: every S-qubit circuit whose registers are Q, P, W has a memory of dimension at most 2^S
--   - generalization: inputs in D, phase oracle with a fixed root ω_d (d = |D|) → any bijection enc : D ≃ ZMod |D| and any ω with ω^{|D|} = 1; reason: the paper fixes one d'th root and one encoding; the Lean statement holds for each choice, the paper's among them (the base goal Theorem 3.5 is stated the same way)
--   - generalization: any quantum algorithm using time T → T is the number of queries; reason: queries never exceed time, so a lower bound on queries implies the printed lower bound on time; the proof (p.42) bounds queries
--   - reading: There is a constant C > 0 … with n sufficiently large → ∃ C > 0, ∃ n₀, chosen before everything else, for all n ≥ n₀; reason: n₀ does not depend on F, M, g, h, c, D, S or the algorithm
--   - encoding: computes the function f_M → CommitsCorrect: all n output coordinates committed and every commit correct; reason: p.43, 'Since f_M has n outputs'
--   - encoding: D ⊆ F with |D| ≥ 2 → D : Finset F with 2 ≤ |D| and an instance NeZero |D|; reason: the phase register ZMod |D| needs |D| ≠ 0, implied by |D| ≥ 2
--   - encoding: space S → S a natural number (number of qubits); reason: S counts qubits
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Theorem 6.6, p.42 (§6); Definition 6.1, p.41; §2.2, p.7; proof pp.42–43

import Mathlib
import Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg_FitsInSpace
import Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg_successProb
import Definitions.Def_QNoiseStab_Supplement_IsRigid

set_option autoImplicit false

namespace QNoiseStab.Supplement

/-- **Theorem 6.6** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §6, p.42): "There is a constant C > 0 such that the following holds:
Let M be an n × n matrix over a field F that is (g, h, c)-rigid with n sufficiently large. Then any
quantum algorithm using time T and space S < min(cg/17, ch/544) that computes the function
f_M : D^n → F^n for D ⊆ F with |D| ≥ 2 given by f_M(x) = Mx with success probability larger than
2^{−S} requires that T ≥ C · cnh/S."

There are an absolute constant `C > 0` and a threshold `n₀` such that for every `n ≥ n₀`, every
field `F`, every `(g, h, c)`-rigid `n × n` matrix `M` over `F` with `0 < c ≤ 1`, every finite `D ⊆ F`
with `|D| ≥ 2` and every `S < min(cg/17, ch/544)`, every `T`-query algorithm using at most `S`
qubits that computes `x ↦ Mx` on `D^n` (all `n` output coordinates committed, all commits
correct) with success probability larger than `2^{−S}` on a uniform input has `T ≥ C·c·n·h/S`.

**Formalization Note** "Time T" is the number of queries, as in the proof (p.42). `0 < c ≤ 1` is
added (the paper's implicit range for the rank fraction `c`; `(g, h, 1)`-rigid is its top case):
with `c < 0` and `g, h` very negative, or with `c` large, `g < 1` and `h` large, every matrix (the
zero matrix included) is `(g, h, c)`-rigid vacuously and the printed bound fails for `f_0 = 0`. `D` is encoded into `ZMod |D|` by any bijection
`enc`, the root `ω` is any `ω` with `ω^{|D|} = 1`, and `[NeZero D.card]` (implied by `|D| ≥ 2`) is
needed for the phase register. -/
theorem theorem_6_6 :
    ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ (F : Type) [Field F] (M : Matrix (Fin n) (Fin n) F) (g h c : ℝ), 0 < c → c ≤ 1 →
        IsRigid M g h c →
      ∀ (D : Finset F) [NeZero D.card], 2 ≤ D.card →
      ∀ S : ℕ, (S : ℝ) < min (c * g / 17) (c * h / 544) →
      ∀ (W V κ : Type) [Fintype W] [DecidableEq W] [Fintype V] [Fintype κ] (T : ℕ)
        (A : SpaceBoundedAlg n D.card W (Fin n) V κ T) (q : V → F) (enc : D ≃ ZMod D.card)
        (ω : ℂ), ω ^ D.card = 1 → A.FitsInSpace S →
        ((2 : ℝ) ^ S)⁻¹ < A.successProb enc ω q (fun x => M.mulVec fun j => (x j : F)) →
        C * c * n * h / S ≤ T := by sorry

end QNoiseStab.Supplement
