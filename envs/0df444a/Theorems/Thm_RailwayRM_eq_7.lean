-- Prove2me | Theorems.Thm_RailwayRM_eq_7
-- name    : RailwayRM.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:06.547234+00:00
-- url     : https://prove2.me/theorems/a70ea7b8-f58b-4ca5-9f80-7f137176dabe
-- title:
--   (7): $R_{D,\kappa}-R^{\pi_1}_{S,\kappa}=O(\sqrt\kappa)$ (corrected: needs $b^*_{u,m}<\bar b_m$)
-- statement:
--   Let $(\vec x^*,\vec y^*,\vec b^*_u)$ be an optimal solution of $P_D$ with $b^*_{u,m}<\bar b_m$ for all $m$. There is a constant $C$ such that for every integer $\kappa\ge1$, with $\pi_1$ built in the $\kappa$-scaled system from $(\vec x^*,\vec y^*,\kappa\vec b^*_u)$,
--   $$\big|R_{D,\kappa}-R^{\pi_1}_{S,\kappa}\big|\le C\sqrt\kappa.$$
--
--   The revenue of $\pi_1$ does not depend on the capacity decisions, so no selection appears.
--
--   Differences from the source:
--   - generalization: itineraries are the N consecutive-leg combinations (Table 1, p. 14) → an arbitrary incidence legs n ⊆ legs; reason: the consecutive-leg incidence is a case, so the Lean statement specializes to the source
--   - generalization: λ⃗_n bounded and continuously differentiable, r bounded and twice differentiable (conditions 1 and 4, pp. 11–12) → not assumed; only convexity of Λ_n and joint concavity of r are kept; reason: every instance of the paper is still an instance; the proofs use neither property
--   - generalization: costs c_o and c_s (p. 13) → any reals c_o ≥ 0, c_s ≥ 0; reason: zero costs are allowed in addition to the paper's costs
--   - encoding: prices are the decisions and λ⃗_n the demand map (pp. 10–11) → rates are the decisions in Λ_n, with price map ζ_n and r_n(v) = v · ζ_n(v); reason: condition 2, p. 11: either rates or prices can be viewed as decision variables; the null price is the rate 0
--   - encoding: expectation E over the arrival process → a finite sum over outcome paths, one outcome per period; reason: at most one customer per period, so the sample space is finite
--   - reading: "the capacities are all scaled by κ" (p. 17) → b̄_m and b̲_m both scale by κ; reason: App. p. 6 says the solution of P_{D,κ} is (x⃗*, y⃗*, κb⃗*_u), which fails if b̲_m does not scale and binds
--   - correction: no condition on b*_{u,m} → hypothesis b*_{u,m} < b̄_m for every m; reason: at b*_{u,m} = b̄_m the threshold of step 2 is 0 and π1 stops after period 1. Counterexample: L = N = M = 1, δ = 1, T = 4, k = 1, b̄ = 1, b̲ = 0, c_o = 0.1, c_s = 1, r(x, y) = x(0.1 − x) + y(3 − y) on [0, 0.3] × [0, 0.6]: the optimum has b* = b̄ and the gap is linear in κ
--   - encoding: O(√κ) in κ ∈ ℕ → ∃ C, ∀ κ ≥ 1 (κ : ℕ+), |·| ≤ C √κ; reason: the bound holds for every κ ≥ 1, not only eventually; C comes before κ
--   - encoding: indices ℓ ∈ {1,…,L}, m ∈ {1,…,M}, n ∈ {1,…,N}, t ∈ {1,…,T} and k seats per coach (Table 1, p. 14) → Fin L, Fin M, Fin N with [NeZero L] [NeZero M] [NeZero N], and fields T ≥ 1, k ≥ 1; reason: the paper indexes from 1, so each set is nonempty and k > 0; max over legs and division by k need it
-- source:
--   Manchiraju et al., SSRN 4112672 (2023-08-22), (7), App. p. 3, PDF p. 35

import Mathlib
import Definitions.Def_RailwayRM_Model
import Definitions.Def_RailwayRM_Policies

namespace RailwayRM

/-- **(7)** (Manchiraju et al., SSRN 4112672 (2023-08-22), (7), App. p. 3, PDF p. 35):
`R_{D,κ} - R^{π₁}_{S,κ} = O(√κ)`. The constant `C` comes before `κ`.

**Formalization Note.** `π₁` in `P_{S,κ}` is built from the solution `(x⃗*, y⃗*, κ b⃗*_u)` of
`P_{D,κ}`, so its threshold is `k (κ b̄_m - ⌊κ b*_{u,m}⌋)`. `R^{π₁}` depends only on the rates, so no
selection of coaches appears. The hypothesis `b*_{u,m} < b̄_m` is that of the corrected Lemma 1. -/
theorem eq_7 {L M N : ℕ} [NeZero L] [NeZero M] [NeZero N] (I : Instance L M N)
    (v : Rates M N) (b : Fin M → ℝ) (hopt : I.IsOptimalD v b) (hb : ∀ m, b m < (I.bMax m : ℝ)) :
    ∃ C : ℝ, ∀ κ : ℕ+,
      |(I.scale κ).detRevenue v - (I.scale κ).revenue ((I.scale κ).pi1Rates v (scaleCoaches κ b))| ≤
        C * Real.sqrt ((κ : ℕ) : ℝ) := by sorry

end RailwayRM
