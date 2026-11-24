-- Prove2me | Theorems.Thm_P2M_ReciprocityTheory_Cheb_normAtPlace_le_norm__43bb5f9414e5
-- name    : P2M_ReciprocityTheory_Cheb_normAtPlace_le_norm__43bb5f9414e5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:38.779205+00:00
-- url     : https://prove2.me/theorems/138064c8-5082-4028-b926-cc45e38febf8
-- title:
--   P2 M Reciprocity Theory Cheb norm At Place le norm  43bb5f9414e5: P2 M Reciprocity Theory Cheb norm At Place le norm  43bb5f9414e5
-- statement:
--   The P2 M Reciprocity Theory Cheb norm At Place le norm  43bb5f9414e5 construction uses the P2 M Reciprocity Theory Cheb norm At Place le norm  43bb5f9414e5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L70-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/Chebotarev/AbsLogSubLogLeOfHalf.lean#L70-L72

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]

theorem P2M_ReciprocityTheory_Cheb_normAtPlace_le_norm__43bb5f9414e5 (w : InfinitePlace E) (z : mixedSpace E) : normAtPlace w z ≤ ‖z‖ := by sorry

alias «ReciprocityTheory».«Cheb».«normAtPlace_le_norm'» := P2M_ReciprocityTheory_Cheb_normAtPlace_le_norm__43bb5f9414e5
