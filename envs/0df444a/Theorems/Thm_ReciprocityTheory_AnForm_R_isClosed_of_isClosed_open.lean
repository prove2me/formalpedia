-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_isClosed_of_isClosed_open
-- name    : ReciprocityTheory.AnForm.R.isClosed_of_isClosed_open
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:31.080558+00:00
-- url     : https://prove2.me/theorems/5d3d9783-1fe0-447b-8655-86620a599e38
-- title:
--   R: is Closed of is Closed open
-- statement:
--   The R construction uses the is Closed of is Closed open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BijOnClosedPointsOfIsIso.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BijOnClosedPointsOfIsIso.lean#L13-L26

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_SecHomSurjective
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BijOnClosedPointsOfIsIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial
noncomputable section
variable {W X : Scheme.{0}} {sW : W ⟶ Spec (.of ℂ)} {sX : X ⟶ Spec (.of ℂ)}

theorem ReciprocityTheory.AnForm.R.isClosed_of_isClosed_open [LocallyOfFiniteType sW] (V : W.Opens) (x : V)
    (hx : IsClosed ({x} : Set V)) : IsClosed ({x.1} : Set W) := by sorry
