-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_PSL_sup_indexWitness_eq_PGL
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.PSL_sup_indexWitness_eq_PGL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T12:42:19.369648+00:00
-- url     : https://prove2.me/theorems/680533f8-a25c-493a-a758-71f50d04e942
-- title:
--   Cartwright Steger: PSL sup index Witness eq PGL
-- statement:
--   The selected determinant class is large enough to generate all of the
--   finite projective group once `PSL` is present.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/FiniteImage.lean#L118-L124
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Congruence/FiniteImage.lean#L118-L124

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Projective_Index
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Congruence_FiniteImage
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
open scoped MatrixGroups

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.PSL_sup_indexWitness_eq_PGL
    (P : BasePrime) (r : Rank) (level : Nat) :
    PSL P r level ⊔ Subgroup.zpowers (indexWitness P r level) = ⊤ := by sorry
