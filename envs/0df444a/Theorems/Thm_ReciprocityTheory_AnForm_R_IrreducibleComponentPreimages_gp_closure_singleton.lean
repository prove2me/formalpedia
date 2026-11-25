-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_gp_closure_singleton
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.gp_closure_singleton
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:33:02.743337+00:00
-- url     : https://prove2.me/theorems/cd724124-ab23-4a20-86b0-c7095c147f70
-- title:
--   Irreducible Component Preimages: gp closure singleton
-- statement:
--   The Irreducible Component Preimages construction uses the gp closure singleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ClosureFromSpecMemCompsH.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ClosureFromSpecMemCompsH.lean#L12-L16

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {W : Scheme.{0}}

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.gp_closure_singleton {x : W} (h : IsIrreducible (closure ({x} : Set W))) :
    h.genericPoint = x := by sorry
