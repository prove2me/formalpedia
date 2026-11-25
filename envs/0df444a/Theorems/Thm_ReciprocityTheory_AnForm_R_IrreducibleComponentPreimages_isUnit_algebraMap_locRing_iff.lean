-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_isUnit_algebraMap_locRing_iff
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.isUnit_algebraMap_locRing_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:58:07.784433+00:00
-- url     : https://prove2.me/theorems/dd82c72b-42c7-44d3-9450-b70fc9da803d
-- title:
--   Irreducible Component Preimages: is Unit algebra Map loc Ring iff
-- statement:
--   The Irreducible Component Preimages construction uses the is Unit algebra Map loc Ring iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L15-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L15-L44

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
noncomputable section
variable {m : ℕ}

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.isUnit_algebraMap_locRing_iff (K : Ideal (MvPolynomial (Fin m) ℂ)) (p : Fin m → ℂ)
    (hp : ∀ h ∈ K, eval p h = 0) (g : MvPolynomial (Fin m) ℂ) :
    IsUnit (algebraMap _ (locRing K p) g) ↔ eval p g ≠ 0 := by sorry
