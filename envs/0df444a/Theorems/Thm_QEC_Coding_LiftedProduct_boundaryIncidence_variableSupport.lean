-- Prove2me | Theorems.Thm_QEC_Coding_LiftedProduct_boundaryIncidence_variableSupport
-- name    : QEC.Coding.LiftedProduct.boundaryIncidence_variableSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:30:27.057684+00:00
-- url     : https://prove2.me/theorems/d8644fa3-967e-4a2c-8409-79c77b0c6dcb
-- title:
--   Lifted Product: boundary Incidence variable Support
-- statement:
--   The Lifted Product construction uses the boundary Incidence variable Support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L857-L892
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/LiftedProduct.lean#L857-L892

import Definitions.Def_QEC_Coding_QLDPC_SourceValidity
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.LiftedProduct
universe u v

theorem QEC.Coding.LiftedProduct.boundaryIncidence_variableSupport
    {F : Type u} {G aRow aCol bRow bCol : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Group G] [Fintype G] [DecidableEq G]
    [Fintype aRow] [DecidableEq aRow]
    [Fintype aCol] [DecidableEq aCol]
    [Fintype bRow] [DecidableEq bRow]
    [Fintype bCol] [DecidableEq bCol]
    (D : Data F G aRow aCol bRow bCol) (q : QubitIndex aRow aCol bRow bCol G) :
    (boundaryIncidence D).variableSupport q =
      (Finset.univ.filter
          (fun c0 : C0Index aRow bRow G => boundary1Matrix D c0 q ≠ 0)).map
        ⟨Sum.inl, Sum.inl_injective⟩ ∪
      (Finset.univ.filter
          (fun c2 : C2Index aCol bCol G => boundary2Matrix D q c2 ≠ 0)).map
        ⟨Sum.inr, Sum.inr_injective⟩ := by sorry
