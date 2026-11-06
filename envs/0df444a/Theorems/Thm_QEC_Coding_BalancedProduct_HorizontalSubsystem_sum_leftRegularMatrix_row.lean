-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_HorizontalSubsystem_sum_leftRegularMatrix_row
-- name    : QEC.Coding.BalancedProduct.HorizontalSubsystem.sum_leftRegularMatrix_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T18:11:11.495313+00:00
-- url     : https://prove2.me/theorems/e4063e93-55dc-4dfd-9742-341b522d5bd2
-- title:
--   Horizontal Subsystem: sum left Regular Matrix row
-- statement:
--   The Horizontal Subsystem construction uses the sum left Regular Matrix row property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L73-L79
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L73-L79

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Mathlib.LinearAlgebra.Finsupp.LSum
import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.HorizontalSubsystem
open Cyclic
universe u v

theorem QEC.Coding.BalancedProduct.HorizontalSubsystem.sum_leftRegularMatrix_row
    {G : Type u} [Group G] [Fintype G]
    (a : MonoidAlgebra (ZMod 2) G) (i : G) :
    (∑ j : G, LiftedProduct.leftRegularMatrix a i j) = augmentation a := by sorry
