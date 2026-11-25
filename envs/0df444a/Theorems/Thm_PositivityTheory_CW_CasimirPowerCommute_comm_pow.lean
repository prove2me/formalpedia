-- Prove2me | Theorems.Thm_PositivityTheory_CW_CasimirPowerCommute_comm_pow
-- name    : PositivityTheory.CW.CasimirPowerCommute.comm_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:49:56.162415+00:00
-- url     : https://prove2.me/theorems/377d74e0-60a0-42ee-a586-ca522de4b356
-- title:
--   Casimir Power Commute: comm pow
-- statement:
--   The Casimir Power Commute construction uses the comm pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/GelfandCentralHolds.lean#L13-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/GelfandCentralHolds.lean#L13-L43

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_GelfandCentralHolds
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
open PositivityTheory.CW.CasimirPowerCommute
variable {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem PositivityTheory.CW.CasimirPowerCommute.comm_pow (E : Fin n → Fin n → Module.End ℂ V) (hE : IsGlRep E) (c d : Fin n) :
    ∀ (k : ℕ) (a b : Fin n), E c d * (Mm E ^ k) a b - (Mm E ^ k) a b * E c d =
      (if d = a then (Mm E ^ k) c b else 0) - (if b = c then (Mm E ^ k) a d else 0) := by sorry
