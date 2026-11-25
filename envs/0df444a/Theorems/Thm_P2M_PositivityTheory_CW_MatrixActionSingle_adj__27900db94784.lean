-- Prove2me | Theorems.Thm_P2M_PositivityTheory_CW_MatrixActionSingle_adj__27900db94784
-- name    : P2M_PositivityTheory_CW_MatrixActionSingle_adj__27900db94784
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T05:02:00.974794+00:00
-- url     : https://prove2.me/theorems/752f5dd6-93e9-50ac-a6b6-1e3b7fc81d9c
-- title:
--   P2 M Positivity Theory CW Matrix Action Single adj  27900db94784: P2 M Positivity Theory CW Matrix Action Single adj  27900db94784
-- statement:
--   The P2 M Positivity Theory CW Matrix Action Single adj  27900db94784 construction uses the P2 M Positivity Theory CW Matrix Action Single adj  27900db94784 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/ColumnMomentsOfSymmetric.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/ColumnMomentsOfSymmetric.lean#L50-L53

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_ColumnMomentsOfSymmetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.MatrixActionSingle
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem P2M_PositivityTheory_CW_MatrixActionSingle_adj__27900db94784 (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E)
    (u w : PiLp 2 fun _ : Fin n => V) :
    inner ℂ (act (Md ε E) u) w = inner ℂ u (act (Mm E) w) := by sorry

alias «PositivityTheory».«CW».«MatrixActionSingle».«adj'» := P2M_PositivityTheory_CW_MatrixActionSingle_adj__27900db94784
