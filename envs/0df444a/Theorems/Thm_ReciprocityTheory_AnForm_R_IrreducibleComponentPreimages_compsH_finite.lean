-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_compsH_finite
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.compsH_finite
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T05:51:46.824842+00:00
-- url     : https://prove2.me/theorems/92fcf0d9-a478-4e0f-bb15-72514b688708
-- title:
--   Irreducible Component Preimages: comps H finite
-- statement:
--   The Irreducible Component Preimages construction uses the comps H finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L50-L54

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

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.compsH_finite [NoetherianSpace α] (T : Set α) : (compsH T).Finite := by sorry
