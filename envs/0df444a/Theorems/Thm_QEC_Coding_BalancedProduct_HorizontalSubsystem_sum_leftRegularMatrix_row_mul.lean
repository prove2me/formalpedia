-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_HorizontalSubsystem_sum_leftRegularMatrix_row_mul
-- name    : QEC.Coding.BalancedProduct.HorizontalSubsystem.sum_leftRegularMatrix_row_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:37:25.686198+00:00
-- url     : https://prove2.me/theorems/936ef7a5-955f-4841-ac7e-efbb77381a28
-- title:
--   Horizontal Subsystem: sum left Regular Matrix row mul
-- statement:
--   The Horizontal Subsystem construction uses the sum left Regular Matrix row mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L121-L126
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/HorizontalSubsystem.lean#L121-L126

import Definitions.Def_QEC_Coding_BalancedProduct_Cyclic
import Definitions.Def_QEC_Coding_ChainComplex_Cohomology
import Definitions.Def_QEC_Coding_CSS_Subsystem
import Mathlib.LinearAlgebra.Finsupp.LSum
import Definitions.Def_QEC_Coding_BalancedProduct_HorizontalSubsystem
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.HorizontalSubsystem
open Cyclic
universe u v

theorem QEC.Coding.BalancedProduct.HorizontalSubsystem.sum_leftRegularMatrix_row_mul
    {G : Type u} [Group G] [Fintype G]
    (a : MonoidAlgebra (ZMod 2) G) (go : G) (c : ZMod 2) :
    (∑ gi : G, LiftedProduct.leftRegularMatrix a go gi * c) =
      augmentation a * c := by sorry
