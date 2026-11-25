-- Prove2me | Theorems.Thm_P2M_Kac_notYet_succ__e7ce5a310839
-- name    : P2M_Kac_notYet_succ__e7ce5a310839
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T13:04:36.384904+00:00
-- url     : https://prove2.me/theorems/cdc20d82-a68b-46be-96b3-720bfc14305a
-- title:
--   P2 M Kac not Yet succ  e7ce5a310839: P2 M Kac not Yet succ  e7ce5a310839
-- statement:
--   The P2 M Kac not Yet succ  e7ce5a310839 construction uses the P2 M Kac not Yet succ  e7ce5a310839 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L188-L198
-- source:
--   https://github.com/zblore/kac-lean/blob/bfeb867d5a9b469cb11139c296e9bd41706e0992/Kac/Basic.lean#L188-L198

module
public import Definitions.Def_Kac_Defs
public import Mathlib.Data.Real.ENatENNReal
public import Mathlib.Dynamics.Ergodic.Conservative
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.MeasureTheory.Integral.Average
public import Definitions.Def_Kac_Basic
set_option autoImplicit false
@[expose] public section
public section
open Set Filter MeasureTheory Topology
open scoped ENNReal
open Kac
variable {α : Type*} {f : α → α} {A : Set α}

theorem P2M_Kac_notYet_succ__e7ce5a310839 (n : ℕ) : notYet f A (n + 1) = notYet f A n ∩ (f^[n] ⁻¹' A)ᶜ := by sorry

alias «Kac».«notYet_succ'» := P2M_Kac_notYet_succ__e7ce5a310839
