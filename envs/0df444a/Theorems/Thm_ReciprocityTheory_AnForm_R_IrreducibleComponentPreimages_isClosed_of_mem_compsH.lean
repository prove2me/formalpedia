-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_isClosed_of_mem_compsH
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.isClosed_of_mem_compsH
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:36.741721+00:00
-- url     : https://prove2.me/theorems/24aa7cb3-c1ce-47ea-b6e6-36d7900a0252
-- title:
--   Irreducible Component Preimages: is Closed of mem comps H
-- statement:
--   The Irreducible Component Preimages construction uses the is Closed of mem comps H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L56-L59

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

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.isClosed_of_mem_compsH {T : Set α} (hT : IsClosed T) {C : Set α} (hC : C ∈ compsH T) :
    IsClosed C := by sorry
