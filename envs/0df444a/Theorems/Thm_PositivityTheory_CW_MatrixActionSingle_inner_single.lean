-- Prove2me | Theorems.Thm_PositivityTheory_CW_MatrixActionSingle_inner_single
-- name    : PositivityTheory.CW.MatrixActionSingle.inner_single
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T08:51:29.681797+00:00
-- url     : https://prove2.me/theorems/30137612-ded1-4770-9045-de124c954c89
-- title:
--   Matrix Action Single: inner single
-- statement:
--   The Matrix Action Single construction uses the inner single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/ColumnMomentsOfSymmetric.lean#L64-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/ColumnMomentsOfSymmetric.lean#L64-L67

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

theorem PositivityTheory.CW.MatrixActionSingle.inner_single (e : Fin n) (v : V) (w : PiLp 2 fun _ : Fin n => V) :
    inner ℂ (PiLp.single 2 e v) w = inner ℂ v (w e) := by sorry
