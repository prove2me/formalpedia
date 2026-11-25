-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AffPres_zero_bdIdeal_iff
-- name    : ReciprocityTheory.AnForm.R.AffPres.zero_bdIdeal_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:45:35.134091+00:00
-- url     : https://prove2.me/theorems/6e237f01-7b08-5209-804f-f30260179258
-- title:
--   Aff Pres: zero bd Ideal iff
-- statement:
--   The Aff Pres construction uses the zero bd Ideal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsBasicOpenCover.lean#L123-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsBasicOpenCover.lean#L123-L137

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsBasicOpenCover
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace IrreducibleComponentPreimages
noncomputable section
variable {W : Scheme.{0}}
variable {s : W ⟶ Spec (.of ℂ)}

theorem ReciprocityTheory.AnForm.R.AffPres.zero_bdIdeal_iff [LocallyOfFiniteType s] (P : AffPres s) (Z : W.IdealSheafData)
    (x : W) (hx : x ∈ P.V) (hc : IsClosed ({x} : Set W)) :
    (∀ g ∈ P.bdIdeal Z, eval (P.coord x hx) g = 0) ↔ x ∈ (Z.support : Set W) := by sorry
