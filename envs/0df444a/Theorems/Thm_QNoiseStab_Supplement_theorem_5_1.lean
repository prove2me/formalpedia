-- Prove2me | Theorems.Thm_QNoiseStab_Supplement_theorem_5_1
-- name    : QNoiseStab.Supplement.theorem_5_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T00:22:29.628986+00:00
-- url     : https://prove2.me/theorems/8c6887f3-396a-4380-b215-d69eae0fcb52
-- title:
--   Theorem 5.1 — sorting in space $S$ needs $T=\Omega(n^{4/3}\log\log n/(S^{1/3}\log n))$ queries
-- statement:
--   There is a constant $c>0$ such that the following holds. Let $m\ge n^2$ and put
--
--   $$
--   \ell=\min\Bigl(S,\ c\,n\Bigl(\frac{\log\log n}{\log n}\Bigr)^{3}\Bigr).
--   $$
--
--   Every quantum query algorithm with $T$ queries and space $S$ (intermediate measurements allowed, outputs committed during the run) that sorts inputs in $[m]^n$ — commits, for every input index $i$, the pair $(x_i,r_i)$ of its value and stable rank, with all commits correct — with probability at least $2^{-\ell}$ on a uniformly random input $x\in[m]^n$ satisfies
--
--   $$
--   T\ \ge\ C\,\frac{n^{4/3}\,\log\log n}{S^{1/3}\,\log n}
--   $$
--
--   for every $n\ge n_0$, where $C>0$ and $n_0$ are constants depending only on $c$.
--
--   This is the first non-trivial time-space tradeoff for sorting against fully general quantum algorithms, which may choose adaptively when to produce each output.
--
--   Differences from the source:
--   - generalization: §2.2 space-bounded circuits: unitaries U_t, flag and output measurements (fully general model of [HM23]) or fixed-time output measurements (output-oblivious model), reset measurements, start state |0⟩ → SpaceBoundedAlg: an arbitrary quantum instrument per step with outcome 'no output' or 'commit (j, v)', and an arbitrary input-independent start density matrix; reason: every §2.2 circuit (fully general or output-oblivious) composes into one instrument per step, so the Lean class contains the paper's and the statement specializes to it
--   - generalization: the algorithm uses S qubits of memory, its whole state stored in qubits → FitsInSpace S: n · d · |W| ≤ 2^S for the memory (Fin n × ZMod d) × W, query and phase registers included; reason: every S-qubit circuit whose registers are Q, P, W has a memory of dimension at most 2^S
--   - generalization: inputs in [m], phase oracle with a fixed root ω_m (d = m) → any bijection enc : Fin m ≃ ZMod m and any ω with ω^m = 1; reason: the paper fixes one d'th root and one encoding; the Lean statement holds for each choice, the paper's among them (the base goal Theorem 3.5 is stated the same way)
--   - reading: T that is Ω(n^{4/3} log log n/(S^{1/3} log n)) → ∃ C > 0, ∃ n₀ (chosen after c, before everything else) with T ≥ C·n^{4/3}·log log n/(S^{1/3}·log n) for all n ≥ n₀; reason: the standard meaning of Ω; C and n₀ do not depend on m, S or the algorithm
--   - encoding: log → Real.log (natural logarithm); reason: a change of base is absorbed by c and C
--   - encoding: sorts inputs in [m]^n (SORT_{n,[m]}, Definitions 5.2–5.3) → CommitsCorrect for sortFun: output coordinate i is (x_i, r_i) with the stable rank r_i, every i committed and every commit correct; reason: p.32, 'it must produce n output values in total'; Definition 5.3 views outputs as i ↦ (v_i, r_i)
--   - encoding: [m], [n] → Fin m, Fin n (0-based, same order); reason: Lean convention
--   - encoding: m ≥ n^2 → n^2 ≤ m together with an instance NeZero m; reason: the phase register ZMod m needs m ≠ 0, which m ≥ n^2 gives for n ≥ 1
--   - encoding: space S → S a natural number (number of qubits); reason: S counts qubits
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Theorem 5.1, p.26 (restated p.31); Definitions 5.2–5.3, p.28; §2.2, p.7; proof pp.31–32

import Mathlib
import Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg_FitsInSpace
import Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg_successProb
import Definitions.Def_QNoiseStab_Supplement_sortFun

set_option autoImplicit false

namespace QNoiseStab.Supplement

/-- **Theorem 5.1** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), p.26, restated p.31): "There is a constant c > 0 such that the
following holds. Let m ≥ n^2. For ℓ = min(S, cn(log log n/ log n)^3), any quantum query algorithm
using T queries and space S that sorts inputs in [m]^n with probability at least 2^{−ℓ} must have T
that is Ω(n^{4/3} log log n/(S^{1/3} log n))."

There are constants `c > 0` and `C > 0` and a threshold `n₀` such that for all `n ≥ n₀`,
`m ≥ n^2` and `S`, every `T`-query algorithm using at most `S` qubits that computes
`SORT_{n,[m]}` (every input index `i` committed with `(x_i, r_i)`, all commits correct) with
probability at least `2^{−ℓ}` on a uniform input in `[m]^n`, `ℓ = min(S, c·n·(log log n/log n)^3)`,
has `T ≥ C·n^{4/3}·log log n/(S^{1/3}·log n)`.

**Formalization Note** `log` is the natural logarithm (a change of base is absorbed by `c` and
`C`). `[m]` is `Fin m`, encoded into `ZMod m` by any bijection `enc`; the root `ω` is any `ω`
with `ω^m = 1`. `[NeZero m]` is needed for the phase register and only excludes `m = 0`, which
`m ≥ n^2` already excludes for `n ≥ 1`. Ω is the pair `C`, `n₀`, chosen after `c` and before
everything else. -/
theorem theorem_5_1 :
    ∃ c : ℝ, 0 < c ∧ ∃ C : ℝ, 0 < C ∧ ∃ n₀ : ℕ, ∀ n m : ℕ, ∀ [NeZero m], n₀ ≤ n → n ^ 2 ≤ m →
      ∀ (S : ℕ) (W V κ : Type) [Fintype W] [DecidableEq W] [Fintype V] [Fintype κ] (T : ℕ)
        (A : SpaceBoundedAlg n m W (Fin n) V κ T) (q : V → Fin m × Fin n) (enc : Fin m ≃ ZMod m)
        (ω : ℂ), ω ^ m = 1 → A.FitsInSpace S →
        (2 : ℝ) ^ (-min (S : ℝ) (c * n * (Real.log (Real.log n) / Real.log n) ^ 3)) ≤
            A.successProb enc ω q sortFun →
        C * (n : ℝ) ^ ((4 : ℝ) / 3) * Real.log (Real.log n) /
            ((S : ℝ) ^ ((1 : ℝ) / 3) * Real.log n) ≤ T := by sorry

end QNoiseStab.Supplement
