-- Prove2me | Theorems.Thm_P2M_FongoSync_lt_asymm__20b31d083484
-- name    : P2M_FongoSync_lt_asymm__20b31d083484
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:02:26.138766+00:00
-- url     : https://prove2.me/theorems/7f70f8db-bf64-44fc-adde-6495d20203c8
-- title:
--   P2 M Fongo Sync lt asymm  20b31d083484: P2 M Fongo Sync lt asymm  20b31d083484
-- statement:
--   The P2 M Fongo Sync lt asymm  20b31d083484 construction uses the P2 M Fongo Sync lt asymm  20b31d083484 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L111-L112
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Register.lean#L111-L112

import Definitions.Def_FongoSync_Clock
import Batteries.Tactic.Alias
import Definitions.Def_FongoSync_Register
set_option autoImplicit false
open FongoSync
open Std
set_option linter.unusedSectionVars false
variable {E K : Type} (cmp : K → K → Ordering) (key : E → K)
variable [TransCmp cmp] [LawfulEqCmp cmp]
variable {cmp key}

theorem P2M_FongoSync_lt_asymm__20b31d083484 {x y : K} (h : cmp x y = .lt) : cmp y x ≠ .lt := by sorry

alias «FongoSync».«lt_asymm'» := P2M_FongoSync_lt_asymm__20b31d083484
