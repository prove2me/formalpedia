-- Prove2me | Theorems.Thm_Stable_Prime_eq_hist_top
-- name    : Stable.Prime.eq_hist_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T20:43:42.476333+00:00
-- url     : https://prove2.me/theorems/56314974-8f90-4601-a691-4de92f838509
-- title:
--   Prime: eq hist top
-- statement:
--   The Prime construction uses the eq hist top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L111-L112
-- source:
--   https://github.com/vikraman/event-structures/blob/cbc44b31dd3613d03da2735597d48fb9d4872fdf/EventStructures/Stable/Prime.lean#L111-L112

import Definitions.Def_EventStructures_Stable_Basic
import Definitions.Def_EventStructures_Stable_Prime
set_option autoImplicit true
open ConfFamily
variable {L : Type*} {F : ConfFamily L}
open Stable
open Stable.Prime

theorem Stable.Prime.eq_hist_top (p : Prime F) : p.val = hist F p.val (top p) := by sorry
