-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_bijOn_closedPoints_of_isIso
-- name    : ReciprocityTheory.AnForm.R.bijOn_closedPoints_of_isIso
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:44:03.877752+00:00
-- url     : https://prove2.me/theorems/65681202-546d-5a36-82e9-26a2add67fc8
-- title:
--   R: bij On closed Points of is Iso
-- statement:
--   The R construction uses the bij On closed Points of is Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BijOnClosedPointsOfIsIso.lean#L28-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/BijOnClosedPointsOfIsIso.lean#L28-L61

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

theorem ReciprocityTheory.AnForm.R.bijOn_closedPoints_of_isIso (π : W ⟶ X) (hπ : π ≫ sX = sW) [LocallyOfFiniteType sW]
    [LocallyOfFiniteType sX] (U : X.Opens) [IsIso (π ∣_ U)] :
    Set.BijOn π.base {x | IsClosed ({x} : Set W) ∧ π.base x ∈ U}
      {y | IsClosed ({y} : Set X) ∧ y ∈ U} := by sorry
