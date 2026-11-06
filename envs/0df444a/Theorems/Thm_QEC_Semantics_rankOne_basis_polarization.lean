-- Prove2me | Theorems.Thm_QEC_Semantics_rankOne_basis_polarization
-- name    : QEC.Semantics.rankOne_basis_polarization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:52:59.139075+00:00
-- url     : https://prove2.me/theorems/d5a0faae-28a0-446a-b329-8403d3975a8d
-- title:
--   Semantics: rank One basis polarization
-- statement:
--   Complex polarization expresses an off-diagonal matrix unit using valid-effect directions.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L120-L148
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/QuditNoInformation.lean#L120-L148

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators ComplexOrder TensorProduct
universe u v

theorem QEC.Semantics.rankOne_basis_polarization {H : Type u}
    [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
    (x y : H) :
    (InnerProductSpace.rankOne Complex x y).toLinearMap =
      (2 : Complex)⁻¹ •
          (InnerProductSpace.rankOne Complex (x + y) (x + y)).toLinearMap +
        Complex.I • ((2 : Complex)⁻¹ •
          (InnerProductSpace.rankOne Complex (x + Complex.I • y)
            (x + Complex.I • y)).toLinearMap) -
        ((1 + Complex.I) * (2 : Complex)⁻¹) •
          ((InnerProductSpace.rankOne Complex x x).toLinearMap +
            (InnerProductSpace.rankOne Complex y y).toLinearMap) := by sorry
