-- Prove2me | Theorems.Thm_PositivityTheory_CW_CharpolyPowerTraces_coeff_succ_zero
-- name    : PositivityTheory.CW.CharpolyPowerTraces.coeff_succ_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:49:13.545606+00:00
-- url     : https://prove2.me/theorems/e8e74657-a990-4b07-8a18-1bd5b032cfcb
-- title:
--   Charpoly Power Traces: coeff succ zero
-- statement:
--   The Charpoly Power Traces construction uses the coeff succ zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/NilpotentOfPowerTraces.lean#L29-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/CasselmanWallach/NilpotentOfPowerTraces.lean#L29-L34

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_GroundTheory_GlobalFields_Artin_LogCharpoly
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_NilpotentOfPowerTraces
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
open PositivityTheory.CW.CharpolyPowerTraces
open Polynomial

theorem PositivityTheory.CW.CharpolyPowerTraces.coeff_succ_zero {R : Type} [CommRing R] [Algebra ℚ R] {n : ℕ} (N : Matrix (Fin n) (Fin n) R)
    (h : ∀ k, (N ^ (k + 1)).trace = 0) (m : ℕ) : N.charpolyRev.coeff (m + 1) = 0 := by sorry
