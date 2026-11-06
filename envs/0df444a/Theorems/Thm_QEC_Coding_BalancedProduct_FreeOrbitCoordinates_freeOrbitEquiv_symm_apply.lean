-- Prove2me | Theorems.Thm_QEC_Coding_BalancedProduct_FreeOrbitCoordinates_freeOrbitEquiv_symm_apply
-- name    : QEC.Coding.BalancedProduct.FreeOrbitCoordinates.freeOrbitEquiv_symm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T20:39:00.182662+00:00
-- url     : https://prove2.me/theorems/5876730a-6c99-4257-9c5c-229726ded2fd
-- title:
--   Free Orbit Coordinates: free Orbit Equiv symm apply
-- statement:
--   The Free Orbit Coordinates construction uses the free Orbit Equiv symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/FreeOrbitCoordinates.lean#L94-L96
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/BalancedProduct/FreeOrbitCoordinates.lean#L94-L96

import Definitions.Def_QEC_Coding_ExpanderCodes_LiftedProduct
import Mathlib.GroupTheory.GroupAction.Quotient
import Definitions.Def_QEC_Coding_BalancedProduct_FreeOrbitCoordinates
set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BalancedProduct QEC.Coding.BalancedProduct.FreeOrbitCoordinates
universe u v
variable (G : Type u) (X : Type v) [Group G] [MulAction G X]

theorem QEC.Coding.BalancedProduct.FreeOrbitCoordinates.freeOrbitEquiv_symm_apply [IsCancelSMul G X]
    (o : OrbitIndex G X) (g : G) :
    (freeOrbitEquiv G X).symm (o, g) = g • orbitRep G X o := by sorry

attribute [defeq] QEC.Coding.BalancedProduct.FreeOrbitCoordinates.freeOrbitEquiv_symm_apply
