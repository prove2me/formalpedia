-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_isClosed_sUnion_compsH_not
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.isClosed_sUnion_compsH_not
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:32:44.784383+00:00
-- url     : https://prove2.me/theorems/983dff09-09db-5685-8dcc-18388a25048e
-- title:
--   Irreducible Component Preimages: is Closed s Union comps H not
-- statement:
--   The Irreducible Component Preimages construction uses the is Closed s Union comps H not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ClosureFromSpecMemCompsH.lean#L170-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ClosureFromSpecMemCompsH.lean#L170-L174

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

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.isClosed_sUnion_compsH_not [IsNoetherian W] {T : Set W} (hT : IsClosed T) (y : W) :
    IsClosed (⋃₀ {D | D ∈ compsH T ∧ y ∉ D}) := by sorry
