-- Prove2me | Theorems.Thm_QEC_Bounds_BPTCommutingProjectorModel_linearMap_eq_zero_of_cross_and_equal_gram
-- name    : QEC.Bounds.BPTCommutingProjectorModel.linearMap_eq_zero_of_cross_and_equal_gram
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T07:30:38.509318+00:00
-- url     : https://prove2.me/theorems/ae978088-96b8-4e86-b2ab-57ad580485fc
-- title:
--   BPTCommuting Projector Model: linear Map eq zero of cross and equal gram
-- statement:
--   A vanishing cross Gram and equal right Gram operators force the first amplitude to vanish.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L382-L426
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Bounds/BPTDisentangling/NoCloning/PartialTrace.lean#L382-L426

import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_ScalarCompression_Transport
import Definitions.Def_QEC_Bounds_BPTDisentangling_NoCloning_PartialTrace
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v
open QEC.Bounds.BPTCommutingProjectorModel
variable {L : BPTQuditLattice} {kappa : Type v} [Fintype kappa]

theorem QEC.Bounds.BPTCommutingProjectorModel.linearMap_eq_zero_of_cross_and_equal_gram
    {N C : Type u}
    [NormedAddCommGroup N] [InnerProductSpace Complex N] [Semantics.FiniteQuantumSystem N]
    [NormedAddCommGroup C] [InnerProductSpace Complex C] [Semantics.FiniteQuantumSystem C]
    (A B : C →ₗ[Complex] N)
    (hcross : A.comp (LinearMap.adjoint B) = 0)
    (hgram : (LinearMap.adjoint A).comp A = (LinearMap.adjoint B).comp B) :
    A = 0 := by sorry
