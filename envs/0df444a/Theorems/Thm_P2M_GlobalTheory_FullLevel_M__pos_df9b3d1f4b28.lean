-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FullLevel_M__pos_df9b3d1f4b28
-- name    : P2M_GlobalTheory_FullLevel_M__pos_df9b3d1f4b28
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:18:26.888545+00:00
-- url     : https://prove2.me/theorems/7129509e-0470-44e9-8e49-f8d0caba3aca
-- title:
--   P2 M Global Theory Full Level M  pos df9b3d1f4b28: P2 M Global Theory Full Level M  pos df9b3d1f4b28
-- statement:
--   The P2 M Global Theory Full Level M  pos df9b3d1f4b28 construction uses the P2 M Global Theory Full Level M  pos df9b3d1f4b28 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSympLevel.lean#L29-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsSympLevel.lean#L29-L29

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_AbelianLawCounterexamples_WeilIsUniqueOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSympLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FullLevel
open ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem P2M_GlobalTheory_FullLevel_M__pos_df9b3d1f4b28 (l : Level H) : 0 < l.M' := by sorry

alias «GlobalTheory».«FullLevel».«M'_pos» := P2M_GlobalTheory_FullLevel_M__pos_df9b3d1f4b28
