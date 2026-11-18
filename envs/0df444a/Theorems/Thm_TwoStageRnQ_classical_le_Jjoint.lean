-- Prove2me | Theorems.Thm_TwoStageRnQ_classical_le_Jjoint
-- name    : TwoStageRnQ.classical_le_Jjoint
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T00:22:02.03838+00:00
-- url     : https://prove2.me/theorems/1d64b128-db90-4b57-976f-6c65a9a1d6a4
-- title:
--   Eq. (22): $\inf C^{\mathrm{lot}}\le\mathcal J(k_1,k_2)$
-- statement:
--   Eq. (22), first inequality: on every demand environment, $\inf_{\Pi\in\mathcal P_{(R,nQ)}}C^{\mathrm{lot}}(\Pi)\le\mathcal J(k_1,k_2)$.
-- source:
--   M. Hu, "A 5/3 Guarantee for Echelon Stock (R,nQ) Policies in Two-Stage Stochastic Serial Systems", manuscript rq_167.tex (Sept. 28, 2026 version); posted as arXiv:2609.06318. Eq. (22); Lemma D.2.

import Definitions.Def_TwoStageRnQ_Model

namespace TwoStageRnQ

theorem classical_le_Jjoint (P : Params) (S : DemandSpace P) :
    (⨅ c : ClassicalControls, classicalLotCost P S c) ≤ ENNReal.ofReal (P.Jjoint P.k1 P.k2) := by sorry

end TwoStageRnQ
