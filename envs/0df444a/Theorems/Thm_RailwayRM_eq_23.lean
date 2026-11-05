-- Prove2me | Theorems.Thm_RailwayRM_eq_23
-- name    : RailwayRM.eq_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:24.900646+00:00
-- url     : https://prove2.me/theorems/e56cfcb5-2c42-4b94-9b8e-be6a7504a0c1
-- title:
--   (23): expected standing passengers under $\tilde\pi_1$
-- statement:
--   Let $(\vec x^*,\vec y^*,\vec b^*_u)$ be an optimal solution of $P_D$. Under $\tilde\pi_1$, for every leg $\ell$ and train $m$,
--   $$\mathbb E\big(\bar Y_{\ell,m}[1,T]-b^*_{u,m}k\big)^+\le\tfrac12\sqrt{\bar y^*_{\ell,m}(1-\bar y^*_{\ell,m})T}+\big(\bar y^*_{\ell,m}T-b^*_{u,m}k\big)^+.$$
--
--   This applies (22) to the binomial count of unreserved passengers on a leg of a train.
--
--   Differences from the source:
--   - generalization: itineraries are the N consecutive-leg combinations (Table 1, p. 14) → an arbitrary incidence legs n ⊆ legs; reason: the consecutive-leg incidence is a case, so the Lean statement specializes to the source
--   - generalization: λ⃗_n bounded and continuously differentiable, r bounded and twice differentiable (conditions 1 and 4, pp. 11–12) → not assumed; only convexity of Λ_n and joint concavity of r are kept; reason: every instance of the paper is still an instance; the proofs use neither property
--   - generalization: costs c_o and c_s (p. 13) → any reals c_o ≥ 0, c_s ≥ 0; reason: zero costs are allowed in addition to the paper's costs
--   - encoding: prices are the decisions and λ⃗_n the demand map (pp. 10–11) → rates are the decisions in Λ_n, with price map ζ_n and r_n(v) = v · ζ_n(v); reason: condition 2, p. 11: either rates or prices can be viewed as decision variables; the null price is the rate 0
--   - encoding: expectation E over the arrival process → a finite sum over outcome paths, one outcome per period; reason: at most one customer per period, so the sample space is finite
--   - encoding: indices ℓ ∈ {1,…,L}, m ∈ {1,…,M}, n ∈ {1,…,N}, t ∈ {1,…,T} and k seats per coach (Table 1, p. 14) → Fin L, Fin M, Fin N with [NeZero L] [NeZero M] [NeZero N], and fields T ≥ 1, k ≥ 1; reason: the paper indexes from 1, so each set is nonempty and k > 0; max over legs and division by k need it
-- source:
--   Manchiraju et al., SSRN 4112672 (2023-08-22), (23), App. p. 5, PDF p. 37

import Mathlib
import Definitions.Def_RailwayRM_Model
import Definitions.Def_RailwayRM_Policies

namespace RailwayRM

/-- **(23)** (Manchiraju et al., SSRN 4112672 (2023-08-22), (23), App. p. 5, PDF p. 37): under `π̃₁`,
`E(Ȳ_{ℓ,m}[1,T] - b*_{u,m} k)⁺ ≤ ½ √(ȳ*_{ℓ,m}(1 - ȳ*_{ℓ,m}) T) + (ȳ*_{ℓ,m} T - b*_{u,m} k)⁺`. -/
theorem eq_23 {L M N : ℕ} [NeZero L] [NeZero M] [NeZero N] (I : Instance L M N)
    (v : Rates M N) (b : Fin M → ℝ) (hopt : I.IsOptimalD v b) (ℓ : Fin L) (m : Fin M) :
    I.expect (I.staticRates v) (fun ω => max ((I.unresCount ω ℓ m : ℝ) - b m * (I.k : ℝ)) 0) ≤
      Real.sqrt (I.ybar v ℓ m * (1 - I.ybar v ℓ m) * (I.T : ℝ)) / 2 +
        max (I.ybar v ℓ m * (I.T : ℝ) - b m * (I.k : ℝ)) 0 := by sorry

end RailwayRM
