-- Prove2me | Theorems.Thm_PositivityTheory_CW_PMaxPr_evalAt_apply
-- name    : PositivityTheory.CW.PMaxPr.evalAt_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:51:19.610711+00:00
-- url     : https://prove2.me/theorems/7cfba8da-2407-4446-9c59-e1158e4398db
-- title:
--   PMax Pr: eval At apply
-- statement:
--   The PMax Pr construction uses the eval At apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/PMaxPr.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/PMaxPr.lean#L18-L19

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

theorem PositivityTheory.CW.PMaxPr.evalAt_apply {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (g : Matrix (Fin n) (Fin n) ℂ)
    (F : V →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (v : V) : evalAt g F v = F v g := by sorry

attribute [defeq] PositivityTheory.CW.PMaxPr.evalAt_apply
