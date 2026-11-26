-- Prove2me | Theorems.Thm_Sabidussi_bracketRightHom_apply
-- name    : Sabidussi.bracketRightHom_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T04:07:39.229811+00:00
-- url     : https://prove2.me/theorems/d1625d60-00cd-4e4d-b4e5-f9a791b9f328
-- title:
--   Sabidussi: bracket Right Hom apply
-- statement:
--   The Sabidussi construction uses the bracket Right Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L70-L70
-- source:
--   https://github.com/gexahedron/sabidussi-lean/blob/58307d74da99ec6e4fe28e012c30c83e369c54c3/Sabidussi/Color.lean#L70-L70

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Definitions.Def_Sabidussi_Color
set_option autoImplicit true
open Sabidussi
open scoped BigOperators

theorem Sabidussi.bracketRightHom_apply (x y : Color) : bracketRightHom x y = bracket x y := by sorry

attribute [defeq] Sabidussi.bracketRightHom_apply
