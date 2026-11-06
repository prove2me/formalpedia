-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_GlobalPlace_comapAlgEquiv_order
-- name    : QEC.Coding.AlgebraicGeometry.GlobalPlace.comapAlgEquiv_order
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:08:12.678552+00:00
-- url     : https://prove2.me/theorems/c744e53a-4eb6-49da-b031-aa7fd71aa9cc
-- title:
--   Global Place: comap Alg Equiv order
-- statement:
--   The Global Place construction uses the comap Alg Equiv order property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/StepPlaceTransport.lean#L38-L41
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Towers/StepPlaceTransport.lean#L38-L41

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_Recursion
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepTransport
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_StepPlaceTransport
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
open QEC.Coding.AlgebraicGeometry.GlobalPlace
variable {k K L : Type*} [Field k] [Finite k]
variable [Field K] [Algebra k K] [Field L] [Algebra k L]

theorem QEC.Coding.AlgebraicGeometry.GlobalPlace.comapAlgEquiv_order (e : K ≃ₐ[k] L)
    (P : GlobalPlace k L) (x : K) :
    (comapAlgEquiv e P).order x = P.order (e x) := by sorry

attribute [defeq] QEC.Coding.AlgebraicGeometry.GlobalPlace.comapAlgEquiv_order
