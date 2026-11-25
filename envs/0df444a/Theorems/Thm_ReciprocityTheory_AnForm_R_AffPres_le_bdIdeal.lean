-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AffPres_le_bdIdeal
-- name    : ReciprocityTheory.AnForm.R.AffPres.le_bdIdeal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:53:35.994806+00:00
-- url     : https://prove2.me/theorems/a450a3d2-285a-549e-bae0-926088368ca1
-- title:
--   Aff Pres: le bd Ideal
-- statement:
--   The Aff Pres construction uses the le bd Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsBasicOpenCover.lean#L115-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsBasicOpenCover.lean#L115-L121

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

theorem ReciprocityTheory.AnForm.R.AffPres.le_bdIdeal (P : AffPres s) (Z : W.IdealSheafData) : P.K ≤ P.bdIdeal Z := by sorry
