-- Prove2me | Theorems.Thm_SingleSampleCombPI_XOS_theorem_3_6
-- name    : SingleSampleCombPI.XOS.theorem_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T09:09:25.736404+00:00
-- url     : https://prove2.me/theorems/f41b7f32-55c4-4d16-951f-d5a89af9a37e
-- title:
--   Theorem 3.6 — smooth single-sample reduction gives β(1−q)Γ(q) (corrected: supremal divisible benchmark)
-- statement:
--   Suppose FDAlg has smooth competitive ratio $\Gamma$ and a valid single-sample single-item algorithm SSPI is $\beta$-competitive when real buyers arrive in the order $\rho$. Then for every $q\in[0,1]$, Algorithm 3 always outputs a feasible allocation, and in the single-sample Game of Googol with real buyers arriving in order $\rho$,
--   $$\mathbb E\Big[\sum_{i=1}^nr'_i(x'_i)\Big]\ \ge\ \beta(1-q)\Gamma(q)\,\mathbb E[\mathrm{Opt}(r')].$$
--   The statement holds for any class of buyer types with supporting prices, in either regime.
--
--   With Theorems 4.1 and 5.1 it gives the goal.
--
--   Differences from the source:
--   - correction: Opt(v) = max over feasible allocations (§2.1, PDF p. 8) → Opt A v = sSup of the welfare of feasible allocations; reason: for divisible items the maximum need not exist: n = 2, m = 1, v₁(0) = 0, v₁(x) = 1 for x > 0, v₂(x) = x, with supporting prices q₁(x) = 1/x (x > 0), q₂ = 1, has feasible welfare approaching 2 but never 2; the supremum equals the maximum whenever it is attained, in particular for indivisible items
--   - generalization: valuations with supporting prices → an arbitrary class C of buyer types contained in the valid ones (C b → b.Valid A); reason: the proof uses only properties of the instances in C; C = Valid A is the source's statement
--   - generalization: single-item algorithm competitive with buyers arriving in index order → for an arbitrary fixed real arrival order ρ: if the single-item algorithm is β-competitive under ρ then the combinatorial algorithm is competitive under ρ; reason: ρ = identity is the source's statement
--   - generalization: Algorithm 3 is a β(1 − q)Γ(q)-competitive SSCombPI algorithm → also: Algorithm 3's output is always feasible; reason: feasibility is part of being an SSCombPI algorithm; stated explicitly as an extra conclusion
--   - encoding: a valuation v with its supporting-price map q_v (and, for computation, oracle access) → a record Buyer m with fields v, q (supporting-price oracle) and d (demand oracle) on vectors in ℝ^m, bundles as indicator vectors; reason: values off A^m are never used; the paper's per-valuation map q_v is the record's q
--   - encoding: an algorithm's internal randomness and expected nonnegative reward → an arbitrary probability space of seeds, with nonnegative lower integrals and finite external random choices averaged inside the seed integrals; independent item seeds use iterated expectations; reason: this includes discrete and atomless randomness; on measurable source payoffs these are ordinary expectations under the independent probability laws, without restricting valuation or allocation domains
--   - encoding: expectations and comparisons of nonnegative real quantities → expectations in ℝ≥0∞ of ENNReal.ofReal of the quantities; reason: all compared quantities are nonnegative under the hypotheses, so no instance changes and no integrability convention is needed
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), SHA-256 d6ed330221fdb64a0d8f70c7d0abbd3346ee1cb8f9e101a745f7e1e57d35230e, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/30.pdf, printed p. 17 / PDF p. 19, Theorem 3.6

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Online

namespace SingleSampleCombPI.XOS

/-- **Theorem 3.6** (Chawla–Dang, STOC 2027 submission #30, printed p. 17 / PDF p. 19).  If
`FDAlg` has smooth competitive ratio `Γ` and the SSPI is a valid single-sample single-item
algorithm that is `β`-competitive under the real arrival order `ρ`, then for every `q ∈ [0,1]`
Algorithm 3 always outputs a feasible allocation and is a `β(1 - q)Γ(q)`-competitive
single-sample combinatorial prophet inequality in the Game of Googol under the order `ρ`.  The buyer class `C` is any class of valuations
with supporting prices; the benchmark is the supremal hindsight optimum. -/
theorem theorem_3_6 (A : Regime) {n m : ℕ} (C : Buyer m → Prop) (hC : ∀ b, C b → b.Valid A)
    (F : FDAlg A n m) (S : KSPI A n 1) (Γ : ℝ → ℝ) (β : ℝ)
    (hF : F.Smooth C Γ) (hSv : S.Valid)
    (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    (∀ (H : Fin n → Bool) (π : Equiv.Perm (Fin n)) (ω : F.Ω) (ωs : Fin m → S.Ω)
        (ρ : Equiv.Perm (Fin n)) (s' r' : Fin n → Buyer m),
        (∀ i, C (s' i)) → (∀ i, C (r' i)) → Feasible A (alg3 F S H π ω ωs ρ s' r')) ∧
    ∀ ρ : Equiv.Perm (Fin n), S.Competitive β ρ →
      ∀ V : Fin n → Fin 2 → Buyer m, (∀ i t, C (V i t)) →
      ENNReal.ofReal (β * (1 - q) * Γ q) * optExp1 (A := A) V ≤ alg3Exp F S q ρ V := by sorry

end SingleSampleCombPI.XOS
