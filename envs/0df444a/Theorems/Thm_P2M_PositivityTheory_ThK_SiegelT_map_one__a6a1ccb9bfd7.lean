-- Prove2me | Theorems.Thm_P2M_PositivityTheory_ThK_SiegelT_map_one__a6a1ccb9bfd7
-- name    : P2M_PositivityTheory_ThK_SiegelT_map_one__a6a1ccb9bfd7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:01.788308+00:00
-- url     : https://prove2.me/theorems/dadc3ae6-5994-4259-9862-aa9df0c5e4cd
-- title:
--   P2 M Positivity Theory Th K Siegel T map one  a6a1ccb9bfd7: P2 M Positivity Theory Th K Siegel T map one  a6a1ccb9bfd7
-- statement:
--   The P2 M Positivity Theory Th K Siegel T map one  a6a1ccb9bfd7 construction uses the P2 M Positivity Theory Th K Siegel T map one  a6a1ccb9bfd7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAlg.lean#L16-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAlg.lean#L16-L17

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_CompactAveragingSplitting_EigenvectorLifting_SiegelTransportAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThK PositivityTheory.ThK.SiegelT
open Matrix GlobalTheory.WeilM
variable {R : Type} [CommRing R] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β ν ν' : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν]
  [Fintype ν'] [DecidableEq ν']

theorem P2M_PositivityTheory_ThK_SiegelT_map_one__a6a1ccb9bfd7 {a : Type} [DecidableEq a] : (1 : Matrix a a E).map c = 1 := by sorry

alias «PositivityTheory».«ThK».«SiegelT».«map_one'» := P2M_PositivityTheory_ThK_SiegelT_map_one__a6a1ccb9bfd7
