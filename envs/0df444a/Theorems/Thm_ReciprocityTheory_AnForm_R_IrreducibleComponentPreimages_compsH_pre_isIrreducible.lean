-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_compsH_pre_isIrreducible
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.compsH_pre_isIrreducible
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:40:23.433808+00:00
-- url     : https://prove2.me/theorems/e5501a67-fdc4-4f77-b0b3-c19a9c8ae38d
-- title:
--   Irreducible Component Preimages: comps H pre is Irreducible
-- statement:
--   The Irreducible Component Preimages construction uses the comps H pre is Irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L27-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
variable {α : Type*} [TopologicalSpace α]

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.compsH_pre_isIrreducible {T C : Set α} (hCT : C ⊆ T) (hC : IsIrreducible C) :
    IsIrreducible ((Subtype.val ⁻¹' C : Set T)) := by sorry
