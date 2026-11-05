-- Prove2me | Theorems.Thm_RailwayRM_eq_21
-- name    : RailwayRM.eq_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:36:11.50031+00:00
-- url     : https://prove2.me/theorems/2c08649f-b73e-411a-831f-4096d4afee55
-- title:
--   (21): expected maximum of reserved demand over legs
-- statement:
--   Let $(\vec x^*,\vec y^*,\vec b^*_u)$ be an optimal solution of $P_D$ and $z_m=T\max\{\bar x^*_{\ell,m}:1\le\ell\le L\}$. Under $\tilde\pi_1$, for every train $m$,
--   $$\mathbb E\Big[\max\big\{\bar X_{\ell,m}[1,T]-z_m:1\le\ell\le L\big\}\Big]\le\sum_{\ell=1}^L\sqrt{\bar x^*_{\ell,m}(1-\bar x^*_{\ell,m})T}.$$
--
--   This bounds the extra reserved coaches that random demand needs beyond the deterministic plan.
--
--   Differences from the source:
--   - generalization: itineraries are the N consecutive-leg combinations (Table 1, p. 14) → an arbitrary incidence legs n ⊆ legs; reason: the consecutive-leg incidence is a case, so the Lean statement specializes to the source
--   - generalization: λ⃗_n bounded and continuously differentiable, r bounded and twice differentiable (conditions 1 and 4, pp. 11–12) → not assumed; only convexity of Λ_n and joint concavity of r are kept; reason: every instance of the paper is still an instance; the proofs use neither property
--   - generalization: costs c_o and c_s (p. 13) → any reals c_o ≥ 0, c_s ≥ 0; reason: zero costs are allowed in addition to the paper's costs
--   - encoding: prices are the decisions and λ⃗_n the demand map (pp. 10–11) → rates are the decisions in Λ_n, with price map ζ_n and r_n(v) = v · ζ_n(v); reason: condition 2, p. 11: either rates or prices can be viewed as decision variables; the null price is the rate 0
--   - encoding: expectation E over the arrival process → a finite sum over outcome paths, one outcome per period; reason: at most one customer per period, so the sample space is finite
--   - encoding: indices ℓ ∈ {1,…,L}, m ∈ {1,…,M}, n ∈ {1,…,N}, t ∈ {1,…,T} and k seats per coach (Table 1, p. 14) → Fin L, Fin M, Fin N with [NeZero L] [NeZero M] [NeZero N], and fields T ≥ 1, k ≥ 1; reason: the paper indexes from 1, so each set is nonempty and k > 0; max over legs and division by k need it
-- source:
--   Manchiraju et al., SSRN 4112672 (2023-08-22), (21), App. p. 5, PDF p. 37

import Mathlib
import Definitions.Def_RailwayRM_Model
import Definitions.Def_RailwayRM_Policies

open Finset

namespace RailwayRM

/-- **(21)** (Manchiraju et al., SSRN 4112672 (2023-08-22), (21), App. p. 5, PDF p. 37): under `π̃₁`,
with `z_m = T max {x̄*_{ℓ,m} : 1 ≤ ℓ ≤ L}`,
`E[max {X̄_{ℓ,m}[1,T] - z_m : 1 ≤ ℓ ≤ L}] ≤ ∑_ℓ √(x̄*_{ℓ,m}(1 - x̄*_{ℓ,m}) T)` for every train `m`. -/
theorem eq_21 {L M N : ℕ} [NeZero L] [NeZero M] [NeZero N] (I : Instance L M N)
    (v : Rates M N) (b : Fin M → ℝ) (hopt : I.IsOptimalD v b) (m : Fin M) :
    I.expect (I.staticRates v)
        (fun ω => univ.sup' univ_nonempty fun ℓ : Fin L =>
          (I.resCount (I.observe ω) ℓ m I.T : ℝ) - (I.T : ℝ) * I.xbarMax v m) ≤
      ∑ ℓ : Fin L, Real.sqrt (I.xbar v ℓ m * (1 - I.xbar v ℓ m) * (I.T : ℝ)) := by sorry

end RailwayRM
