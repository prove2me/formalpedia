-- Prove2me | Theorems.Thm_PositivityTheory_CW_PMaxPr_sq_bound
-- name    : PositivityTheory.CW.PMaxPr.sq_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:50:53.29135+00:00
-- url     : https://prove2.me/theorems/ee4549d9-8bd8-5745-a5b4-3727b4afda6c
-- title:
--   PMax Pr: sq bound
-- statement:
--   The PMax Pr construction uses the sq bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/PMaxPr.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/PMaxPr.lean#L21-L23

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_PMaxPr
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
open PositivityTheory.CW.PMaxPr

theorem PositivityTheory.CW.PMaxPr.sq_bound (x C w : ℝ) (N : ℕ) (h : x ≤ C * w ^ N) (hx : 0 ≤ x) : x ^ 2 ≤ C ^ 2 * w ^ (2 * N) := by sorry
