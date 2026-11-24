-- Prove2me | Theorems.Thm_P2M_PositivityTheory_ThK_SiegelT_map_mul__f92fda10766b
-- name    : P2M_PositivityTheory_ThK_SiegelT_map_mul__f92fda10766b
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:08.002299+00:00
-- url     : https://prove2.me/theorems/ba61b5b8-23c1-490f-ba98-a1ccd99d83e2
-- title:
--   P2 M Positivity Theory Th K Siegel T map mul  f92fda10766b: P2 M Positivity Theory Th K Siegel T map mul  f92fda10766b
-- statement:
--   The P2 M Positivity Theory Th K Siegel T map mul  f92fda10766b construction uses the P2 M Positivity Theory Th K Siegel T map mul  f92fda10766b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAlg.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/CompactAveragingSplitting/EigenvectorLifting/SiegelTransportAlg.lean#L13-L14

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

theorem P2M_PositivityTheory_ThK_SiegelT_map_mul__f92fda10766b {a b e : Type} [Fintype b] (A : Matrix a b E) (B : Matrix b e E) : (A * B).map c = A.map c * B.map c := by sorry

alias «PositivityTheory».«ThK».«SiegelT».«map_mul'» := P2M_PositivityTheory_ThK_SiegelT_map_mul__f92fda10766b
