-- Prove2me | Theorems.Thm_QNoiseStab_Supplement_theorem_4_3
-- name    : QNoiseStab.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T00:21:43.556193+00:00
-- url     : https://prove2.me/theorems/4d5d17b4-ab18-43d6-95c1-5e44ec008e31
-- title:
--   Theorem 4.3 — almost every member of a strongly universal hash family needs $T=\Omega(mn/S)$ queries in space $S$
-- statement:
--   Let $H$ be a strongly universal family of hash functions from $\{0,1\}^n$ to $\{0,1\}^m$ with $n\ge m$, and for a space bound $S$ put
--
--   $$
--   \ell(S)=\min\Bigl(S,\ \frac m{1024}\Bigr).
--   $$
--
--   There are an absolute constant $C>0$ and a threshold $m_0$ such that for all $m\ge m_0$, all $n\ge m$, every such $H$ and every $S$ the following holds. All functions $h\in H$ outside an exceptional set of at most a $2^{-9\ell(S)}$ fraction of $H$ are hard for every space bound $S'\ge S$: every quantum query algorithm that uses at most $S'$ qubits of memory, computes $h$ (commits all $m$ output bits, all correctly) with probability at least $2^{-\ell(S')}$ on a uniformly random input $x\in\{0,1\}^n$, and makes $T$ queries, satisfies
--
--   $$
--   T\ \ge\ C\,\frac{m\,n}{S'} .
--   $$
--
--   Taking $S'=S$ gives the first sentence of the theorem: for all but a $2^{-9\ell}$ fraction of $h\in H$, success $2^{-\ell}$ in space $S$ requires $T=\Omega(mn/S)$. The bound matches the classical tradeoff of Mansour, Nisan and Tiwari, extends it to quantum algorithms with intermediate measurements, and makes individual hash functions hard; for the multiplication family it gives the time-space lower bound for integer multiplication (Corollary 4.5).
--
--   Differences from the source:
--   - generalization: §2.2 space-bounded circuits: unitaries U_t, flag and output measurements (fully general model of [HM23]) or fixed-time output measurements (output-oblivious model), reset measurements, start state |0⟩ → SpaceBoundedAlg: an arbitrary quantum instrument per step with outcome 'no output' or 'commit (j, v)', and an arbitrary input-independent start density matrix; reason: every §2.2 circuit (fully general or output-oblivious) composes into one instrument per step, so the Lean class contains the paper's and the statement specializes to it
--   - generalization: the algorithm uses S qubits of memory, its whole state stored in qubits → FitsInSpace S: n · d · |W| ≤ 2^S for the memory (Fin n × ZMod d) × W, query and phase registers included; reason: every S-qubit circuit whose registers are Q, P, W has a memory of dimension at most 2^S
--   - generalization: inputs in {0,1}, phase oracle with a fixed root ω_d (d = 2) → any bijection enc : Bool ≃ ZMod 2 and any ω with ω^2 = 1; reason: the paper fixes one d'th root and one encoding; the Lean statement holds for each choice, the paper's among them (the base goal Theorem 3.5 is stated the same way)
--   - reading: for sufficiently large m … must make a number of queries T that is Ω(mn/S) → ∃ C > 0, ∃ m₀, chosen before everything else, with T ≥ C·m·n/S′ for all m ≥ m₀; reason: the standard meaning of Ω and of 'sufficiently large'; C and m₀ do not depend on n, H, S or the algorithm
--   - reading: Moreover, this statement also holds if functions identified as hard for space S must be hard for all space bounds S′ such that S ≤ S′ → one exceptional set Bad_S of at most a 2^{−9ℓ(S)} fraction serves every S′ ≥ S, with success threshold 2^{−ℓ(S′)} and bound C·m·n/S′; reason: the strong form of the 'Moreover' clause; S′ = S gives the first sentence
--   - encoding: computes the function h → CommitsCorrect: all m output bits committed and every commit correct; reason: p.20, 'each hash function h requires m output bits to be produced'
--   - encoding: a family H, all but a 2^{−9ℓ} fraction of functions h ∈ H → an indexed family H : ι → ({0,1}^n → {0,1}^m) and a set Bad of indices with |Bad| ≤ 2^{−9ℓ}·|ι|; reason: Pr_{h∈H} in Definition 4.1 is over a uniform member of the family, multiplicities included
--   - encoding: space bound S → S, S′ natural numbers (numbers of qubits); ℓ = min(S, m/1024) real; reason: S counts qubits
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Theorem 4.3, p.19 (§4.1); Definition 4.1, p.17; §2.2, p.7; proof pp.20–21

import Mathlib
import Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg_FitsInSpace
import Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg_successProb
import Definitions.Def_QNoiseStab_Supplement_IsStronglyUniversal

set_option autoImplicit false

namespace QNoiseStab.Supplement

/-- **Theorem 4.3** (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §4.1, p.19): "Let H be a strongly universal family of hash functions
from {0,1}^n to {0,1}^m for n ≥ m for sufficiently large m. Let S be a space bound and
ℓ = min(S, m/1024). For all but a 2^{−9ℓ} fraction of functions h ∈ H, any quantum query
algorithm that computes the function h using S qubits of memory, and succeeds with probability at
least 2^{−ℓ} on inputs uniformly chosen from {0,1}^n, must make a number of queries T that is
Ω(mn/S). Moreover, this statement also holds if functions identified as hard for space S must be
hard for all space bounds S′ such that S ≤ S′."

Stated in the strong ("Moreover") form: there are an absolute constant `C > 0` and a threshold
`m₀` such that for all `m ≥ m₀`, `n ≥ m`, every strongly universal indexed family `H` and every
`S`, some set `Bad` of at most a `2^{−9 ℓ(S)}` fraction of the indices has the property: for every
`i ∉ Bad`, every `S′ ≥ S` and every `T`-query algorithm using at most `S′` qubits that computes
`h_i` (all `m` output bits committed, all commits correct) with success probability at least
`2^{−ℓ(S′)}` on a uniform input, `T ≥ C·m·n/S′`. Here `ℓ(S) = min(S, m/1024)`.

**Formalization Note** The model is `SpaceBoundedAlg` (one instrument per step; the query and
phase registers count against the space). Bits are `Bool`, encoded into `ZMod 2` by any bijection
`enc`; the oracle's root `ω` is any `ω` with `ω^2 = 1`. The output coordinates are the `m` bits of
`h(x)`. Ω and "sufficiently large" are the constants `C`, `m₀`, chosen before everything else. -/
theorem theorem_4_3 :
    ∃ C : ℝ, 0 < C ∧ ∃ m₀ : ℕ, ∀ m n : ℕ, m₀ ≤ m → m ≤ n →
      ∀ (ι : Type) [Fintype ι] (H : ι → (Fin n → Bool) → (Fin m → Bool)),
        IsStronglyUniversal H →
      ∀ S : ℕ, ∃ Bad : Finset ι,
        (Bad.card : ℝ) ≤ (2 : ℝ) ^ (-9 * min (S : ℝ) ((m : ℝ) / 1024)) * Fintype.card ι ∧
        ∀ i, i ∉ Bad → ∀ S' : ℕ, S ≤ S' →
        ∀ (W V κ : Type) [Fintype W] [DecidableEq W] [Fintype V] [Fintype κ] (T : ℕ)
          (A : SpaceBoundedAlg n 2 W (Fin m) V κ T) (q : V → Bool) (enc : Bool ≃ ZMod 2)
          (ω : ℂ), ω ^ 2 = 1 → A.FitsInSpace S' →
          (2 : ℝ) ^ (-min (S' : ℝ) ((m : ℝ) / 1024)) ≤ A.successProb enc ω q (fun x => H i x) →
          C * m * n / S' ≤ T := by sorry

end QNoiseStab.Supplement
