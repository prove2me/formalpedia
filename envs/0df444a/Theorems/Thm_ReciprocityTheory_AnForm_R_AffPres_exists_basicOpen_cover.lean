-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AffPres_exists_basicOpen_cover
-- name    : ReciprocityTheory.AnForm.R.AffPres.exists_basicOpen_cover
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:52:16.529643+00:00
-- url     : https://prove2.me/theorems/20a523a3-85a1-4eb3-bb9c-3d2e59e9cfbd
-- title:
--   Aff Pres: exists basic Open cover
-- statement:
--   The Aff Pres construction uses the exists basic Open cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsBasicOpenCover.lean#L139-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsBasicOpenCover.lean#L139-L147

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

theorem ReciprocityTheory.AnForm.R.AffPres.exists_basicOpen_cover (P : AffPres s) (O : W.Opens) :
    ∃ T : Set (MvPolynomial (Fin P.n) ℂ), ∀ y ∈ P.V,
      (y ∈ O ↔ ∃ g ∈ T, y ∈ W.basicOpen (P.secHom g)) := by sorry
