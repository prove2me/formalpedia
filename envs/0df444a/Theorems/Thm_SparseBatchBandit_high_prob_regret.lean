-- Prove2me | Theorems.Thm_SparseBatchBandit_high_prob_regret
-- name    : SparseBatchBandit.high_prob_regret
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:35:46.668181+00:00
-- url     : https://prove2.me/theorems/fdb4b710-23d5-4c66-bd6a-3596b9436a91
-- title:
--   §4.2.3, p.18 — high-probability regret bound
-- statement:
--   Under the standing hypotheses, there are $C',C,c_1,c_2>0$ depending only on $A,\varepsilon,\beta,p$ such that with probability at least
--
--   $$
--   1-(2+M)T^{-2}-2M^2\exp\Big(C\frac{s_0\log K\log d}{\gamma\rho}-c_1\frac{\rho^2\sqrt{Ts_0}}{M}\Big)-M\exp\Big(\log d-\log K\cdot c_2\frac{\sqrt{Ts_0}}{M}\Big),
--   $$
--
--   the regret of LBGL satisfies
--
--   $$
--   R_T\le\frac{C'}{\gamma\rho}\cdot M^{3/2}\cdot\sqrt{\log K\log(KT)\log(dT)}\cdot\sqrt{Ts_0}\cdot\Big(\frac{T}{s_0}\Big)^{\frac{1}{2(2^M-1)}} .
--   $$
--
--   This is the step before the expected-regret bound of Theorem 2.
--
--   Differences from the source:
--   - reading: Assumption 1's display, at unit v only → HasSubgaussianMGF of ⟨v, x⟩ with proxy 1, for every λ and unit v; reason: the unit-scale bound is not sub-Gaussianity; §2.1 and p.18 use every scale
--   - reading: O, Ω and Poly with numerical constants → ∀ A ε β p, ∃ constants, ∀ instance; reason: the implied constants of the hypotheses are the only reading under which a bound can hold: a constant uniform over them would allow d = exp(T)
--   - reading: b = Θ(√T (T/s₀)^(1/(2(2^M−1)))), t₁ = b√s₀, t_m = ⌊b√t_{m−1}⌋, t_M = T → exact b, floors on every t_m, each capped at T, last point T; reason: the page leaves b open up to Θ, and a grid point is a round; this b makes the unrounded recursion end exactly at T
--   - reading: each batch is partitioned into M intervals evenly → q-th round in T_m^(j) iff ⌊(j−1)n/M⌋ < q ≤ ⌊jn/M⌋; reason: the page gives no formula; this is the even floor partition
--   - reading: no statement on the joint law of contexts and noises → the context family is independent of the noise family; reason: the proof on p.28 conditions on the selected contexts and uses this
--   - reading: a* = argmax without a tie-break in Assumption 2 → lowest-index maximizer, the rule of Algorithm 1; reason: the proof applies Assumption 2 at θ̂₀ = 0, where all arms tie
--   - generalization: θ̂_m is the argmin → θ̂_m is the output of an arbitrary measurable selection of minimizers; reason: the argmin need not be unique; the statement covers every choice, so it specializes to any rule the paper could mean
--   - generalization: M = O(log log(T/s₀)) → M ≤ A max(1, log log(T/s₀)); reason: keeps the small instances with log log(T/s₀) ≤ 1; large instances are the paper's
--   - encoding: no explicit ranges → T ≥ 2, d ≥ 1, K ≥ 2, M ≥ 1, s₀ ≥ 1, γ, ρ > 0; reason: the formulas degenerate outside them: K = 1 gives log K = 0 and T = 1, d = 1 makes the right side 0
--   - encoding: vectors in ℝ^d, rounds 1..T → Fin d → ℝ with the published l2Norm; rounds Fin T, round t + 1 of the page being t; reason: Lean convention; same instances
-- source:
--   Ren, Zhou, Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits, arXiv:2008.11918v4, §4.2.3, p.18

import Mathlib
import Definitions.Def_SparseBatchBandit_Standing
import Definitions.Def_SparseBatchBandit_action
import Definitions.Def_SparseBatchBandit_regret
import Definitions.Def_SparseBatchBandit_regretRate
open MeasureTheory ProbabilityTheory Matrix

namespace SparseBatchBandit

/-- **High-probability regret bound**, Ren, Zhou, *Dynamic Batch Learning in High-Dimensional Sparse Linear Contextual Bandits*, arXiv:2008.11918v4, §4.2.3, p.18 (PDF 18). With probability at least
`1 − (2 + M) T⁻² − 2M² exp(O(s₀ log K log d/(γρ)) − Ω(ρ²√(Ts₀)/M)) − M exp(log d − log K · Ω(√(Ts₀)/M))`,
`R_T(Alg) ≤ (C″/(γρ)) · M^{3/2} · √(log K log(KT) log(dT)) · √(Ts₀) · (T/s₀)^{1/(2(2^M−1))}`.

**Formalization Note.** `C″`, the `O` and the two `Ω` become `C'`, `C`, `c₁`, `c₂`, chosen before the
instance, so they depend only on `A, ε, β, p`. -/
theorem high_prob_regret (A ε β : ℝ) (p : ℕ) (_hA : 0 < A) (_hε : 0 < ε) (_hβ : 0 < β) :
    ∃ C' C c₁ c₂ : ℝ, 0 < C' ∧ 0 < C ∧ 0 < c₁ ∧ 0 < c₂ ∧
      ∀ (T d K M s₀ : ℕ) [NeZero K] (γ ρ : ℝ)
        (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (x : Ω → Fin T → Fin K → Fin d → ℝ) (ξ : Ω → Fin T → ℝ) (θstar : Fin d → ℝ)
        (sel : LassoSelector T s₀ M d),
        Standing A ε β p γ ρ P x ξ θstar sel →
          1 - (2 + (M : ℝ)) * ((T : ℝ) ^ 2)⁻¹ -
              2 * (M : ℝ) ^ 2 * Real.exp (C * (s₀ * Real.log K * Real.log d / (γ * ρ)) -
                c₁ * ρ ^ 2 * Real.sqrt ((T : ℝ) * s₀) / M) -
              (M : ℝ) * Real.exp (Real.log d -
                Real.log K * (c₂ * Real.sqrt ((T : ℝ) * s₀) / M)) ≤
            P.real {ω | regret (x ω) θstar (action s₀ M sel (x ω) (ξ ω) θstar) ≤
              C' * regretRate T d K M s₀ γ ρ} := by sorry

end SparseBatchBandit
