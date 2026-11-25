-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_image_mem_compsH
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.image_mem_compsH
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:57.901796+00:00
-- url     : https://prove2.me/theorems/b3a4ee59-9afc-5ac0-8bbd-3dda266c4d1e
-- title:
--   Irreducible Component Preimages: image mem comps H
-- statement:
--   The Irreducible Component Preimages construction uses the image mem comps H property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L32-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/PreMemIrreducibleComponents.lean#L32-L39

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

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.image_mem_compsH {T : Set α} {A : Set T} (hA : A ∈ irreducibleComponents T) :
    Subtype.val '' A ∈ compsH T := by sorry
