-- Prove2me | Theorems.Thm_P2M_Auto_aux_add_inf__657294d4941d
-- name    : P2M_Auto_aux_add_inf__657294d4941d
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:39:29.785063+00:00
-- url     : https://prove2.me/theorems/dd78b80b-8b4d-58a1-b270-0ec82f678901
-- title:
--   P2 M Auto aux add inf  657294d4941d: P2 M Auto aux add inf  657294d4941d
-- statement:
--   The P2 M Auto aux add inf  657294d4941d construction uses the P2 M Auto aux add inf  657294d4941d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L681-L684
-- source:
--   https://github.com/roos-j/lean-nct/blob/3e09aa52c478ec69abb02eb250c5e5ed06653c3a/LeanNct/Auto/CalderonTransference.lean#L681-L684

module
public import Mathlib
public import Definitions.Def_LeanNct_Auto_CalderonTransference
set_option autoImplicit true
@[expose] public section
public section
open Auto
universe u
open MeasureTheory Set
open scoped BigOperators ENNReal
noncomputable section

theorem P2M_Auto_aux_add_inf__657294d4941d {ι : Type*} (q : Finset ι) (hq : q.Nonempty)
    (f : ι → ℝ) (a : ℝ) :
    a + q.inf' hq f = q.inf' hq (fun i ↦ a + f i) := by sorry

alias «Auto».«aux_add_inf'» := P2M_Auto_aux_add_inf__657294d4941d
