-- Prove2me | Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_addVal_prod
-- name    : ReciprocityTheory.MultiplicativeHeights.addVal_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:21:41.080624+00:00
-- url     : https://prove2.me/theorems/49894bbf-5aa7-4ad8-a973-2694244bcf88
-- title:
--   Multiplicative Heights: add Val prod
-- statement:
--   The Multiplicative Heights construction uses the add Val prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/DetSubtypeCompAssociatedProd.lean#L18-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/SemistableReduction/DetSubtypeCompAssociatedProd.lean#L18-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_ComapInclusionIsLocalHom
import Definitions.Def_Lemmata_GeneralBFactLast_Imports
import Definitions.Def_Lemmata_GeneralBFactTail_Imports
import Definitions.Def_ReciprocityTheory_SemistableReduction_DetSubtypeCompAssociatedProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Module Submodule

theorem ReciprocityTheory.MultiplicativeHeights.addVal_prod {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ι : Type*} (s : Finset ι) (a : ι → O) :
    IsDiscreteValuationRing.addVal O (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal O (a i) := by sorry
