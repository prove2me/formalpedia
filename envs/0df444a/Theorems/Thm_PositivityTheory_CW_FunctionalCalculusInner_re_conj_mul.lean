-- Prove2me | Theorems.Thm_PositivityTheory_CW_FunctionalCalculusInner_re_conj_mul
-- name    : PositivityTheory.CW.FunctionalCalculusInner.re_conj_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:50:16.177709+00:00
-- url     : https://prove2.me/theorems/d33ffe85-bad4-5181-9669-e6a998613d87
-- title:
--   Functional Calculus Inner: re conj mul
-- statement:
--   The Functional Calculus Inner construction uses the re conj mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/FunctionalCalculusOfBasic.lean#L58-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/FunctionalCalculusOfBasic.lean#L58-L60

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusOfBasic
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
open PositivityTheory.CW.FunctionalCalculusInner
variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type}

theorem PositivityTheory.CW.FunctionalCalculusInner.re_conj_mul (z : ℂ) (r : ℝ) : (starRingEnd ℂ z * ((r : ℂ) * z)).re = r * ‖z‖ ^ 2 := by sorry
