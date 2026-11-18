-- Prove2me | Theorems.Thm_TwoStageRnQ_impossibility
-- name    : TwoStageRnQ.impossibility
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T00:21:59.585066+00:00
-- url     : https://prove2.me/theorems/39a8caa8-94dc-45cb-a49e-5a02efdfbf1d
-- title:
--   Theorem 2: a lower limit for the classical policy class
-- statement:
--   Theorem 2: for every $r<(1+\sqrt3)/2$ some instance with all data positive has $\inf C^{\mathrm{sh}}>r\,\mathrm{OPT}^{\mathrm{sh}}$ and $\inf C^{\mathrm{lot}}>r\,\mathrm{OPT}^{\mathrm{sh}}$ on every demand environment.
-- source:
--   M. Hu, "A 5/3 Guarantee for Echelon Stock (R,nQ) Policies in Two-Stage Stochastic Serial Systems", manuscript rq_167.tex (Sept. 28, 2026 version); posted as arXiv:2609.06318. Theorem 2, eq. (28); Appendix E.

import Definitions.Def_TwoStageRnQ_Model

namespace TwoStageRnQ

theorem impossibility (r : ℝ) (hr : r < (1 + Real.sqrt 3) / 2) :
    ∃ P : Params, 0 < P.lam ∧ 0 < P.L1 ∧ 0 < P.L2 ∧ 0 < P.h1 ∧ 0 < P.h2 ∧ 0 < P.p ∧
      0 < P.K1 ∧ 0 < P.K2 ∧
      ∀ S : DemandSpace P,
        ENNReal.ofReal r * OPTsh P < ⨅ c : ClassicalControls, classicalShipCost P S c ∧
        ENNReal.ofReal r * OPTsh P < ⨅ c : ClassicalControls, classicalLotCost P S c := by sorry

end TwoStageRnQ
