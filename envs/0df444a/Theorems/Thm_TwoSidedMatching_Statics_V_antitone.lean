-- Prove2me | Theorems.Thm_TwoSidedMatching_Statics_V_antitone
-- name    : TwoSidedMatching.Statics.V_antitone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T09:27:53.666074+00:00
-- url     : https://prove2.me/theorems/b4b05919-0371-4af8-b7b0-ba2faccb9ba3
-- title:
--   Supplemental Note p. 5 — virtual surplus decreases with matched volume
-- statement:
--   For positive arrival rates and horizon, let $V(\mu)$ be the buyer virtual value at the buyer quantile for volume $\mu$ minus the seller virtual cost at the seller quantile. Under Assumptions 1 and 2, $V$ is weakly decreasing throughout the feasible volume interval:
--
--   $$0\le\mu_1\le\mu_2\le\min\{\lambda^dT,\lambda^sT\}\quad\Longrightarrow\quad V(\mu_2)\le V(\mu_1).$$
--
--   This is the monotonicity used in the proof of Lemma S.5 and the price comparisons.
--
--   **Formalization Note** Density continuity makes the inverse quantiles unambiguous. This inequality applies regardless of the sign of seller costs.
-- source:
--   Chen and Hu, Pricing and Matching with Forward-looking Buyers and Sellers, submitted manuscript (SSRN 2859864, TSpace copy), Supplemental Note p. 5 (PDF 45), proof of Lemma S.5, 'V_i(mu) is decreasing'

import Mathlib
import Definitions.Def_TwoSidedMatching_Statics_Fluid

namespace TwoSidedMatching.Statics

/-- Supplemental Note p. 5, proof of Lemma S.5: virtual surplus decreases
with the proposed matched volume on its feasible interval. -/
theorem V_antitone (E : Environment) (lamD lamS T : ℝ)
    (hcontB : ContinuousOn E.fB (Set.Icc E.loB E.hiB))
    (hcontS : ContinuousOn E.fS (Set.Icc E.loS E.hiS))
    (hreg : E.Regular) (hcross : E.loS ≤ E.hiB)
    (hd : 0 < lamD) (hs : 0 < lamS) (hT : 0 < T) :
    AntitoneOn (V E lamD lamS T) (Set.Icc 0 (min (lamD * T) (lamS * T))) := by sorry

end TwoSidedMatching.Statics
