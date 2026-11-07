-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_PSL_sup_indexB_eq_PGL
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.PSL_sup_indexB_eq_PGL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:48:47.959273+00:00
-- url     : https://prove2.me/theorems/b757b7e7-ee04-434b-aee1-f1e9e0bdcea1
-- title:
--   Cartwright Steger: PSL sup index B eq PGL
-- statement:
--   `whatisr` at the full-index `Chooseorder` place: the genuine `b` formula
--   and `PSL` generate the entire finite projective group.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L157-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/IndexRepresentation.lean#L157-L163

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Norm_Norm
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexSplitting
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_IndexRepresentation
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.PSL_sup_indexB_eq_PGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    PSL P r level ⊔ Subgroup.zpowers (indexB P r level) = ⊤ := by sorry
