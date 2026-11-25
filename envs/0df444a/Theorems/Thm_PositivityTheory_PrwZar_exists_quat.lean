-- Prove2me | Theorems.Thm_PositivityTheory_PrwZar_exists_quat
-- name    : PositivityTheory.PrwZar.exists_quat
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:50:58.578263+00:00
-- url     : https://prove2.me/theorems/a61e2aa1-8481-4d81-b76d-14b6d2f5a14d
-- title:
--   Prw Zar: exists quat
-- statement:
--   The Prw Zar construction uses the exists quat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/ExistsQuat.lean#L5-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AbelianHeightsDuality/ZarhinTrick/ExistsQuat.lean#L5-L17

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_ZarhinTrick_ExistsQuat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.PrwZar

theorem PositivityTheory.PrwZar.exists_quat (n : ℕ) : ∃ α : Matrix (Fin 4) (Fin 4) ℤ,
    α.transpose * α = (n : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) ∧
    α * α.transpose = (n : ℤ) • (1 : Matrix (Fin 4) (Fin 4) ℤ) := by sorry
