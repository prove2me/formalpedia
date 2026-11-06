-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_rightTensorCoefficients_mem_carrier_of_rightMarginal_supportedOn
-- name    : QEC.Semantics.QuditSubsystem.rightTensorCoefficients_mem_carrier_of_rightMarginal_supportedOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:19:56.884362+00:00
-- url     : https://prove2.me/theorems/8b54121a-fd50-46ad-936f-f4f0cd49a527
-- title:
--   Qudit Subsystem: right Tensor Coefficients mem carrier of right Marginal supported On
-- statement:
--   The Qudit Subsystem construction uses the right Tensor Coefficients mem carrier of right Marginal supported On property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L710-L802
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L710-L802

import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Semantics_Entropy_MatrixRelative
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditReplacement
import Definitions.Def_QEC_Semantics_ErrorCorrection_KLRecovery
import Definitions.Def_QEC_Semantics_ErrorCorrection_Detectability
import Definitions.Def_QEC_Semantics_ErrorCorrection_ReferenceDecoupling
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Semantics
open Classical
open DensityOperator
open scoped BigOperators ComplexOrder TensorProduct
universe u v w
open QEC.Semantics.QuditSubsystem
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {q : ι → Nat}

theorem QEC.Semantics.QuditSubsystem.rightTensorCoefficients_mem_carrier_of_rightMarginal_supportedOn
    {H K : Type u} [NormedAddCommGroup H] [InnerProductSpace Complex H]
    [FiniteQuantumSystem H] [NormedAddCommGroup K] [InnerProductSpace Complex K]
    [FiniteQuantumSystem K] (C : QuantumCode H)
    (b : OrthonormalBasis (Fin (Module.finrank Complex K)) Complex K)
    (psi : CompositeSystem H K) (hpsi : ‖psi‖ ^ 2 = 1)
    (hsupported : DensityOperator.SupportedOn C
      (rightMarginal (pureDensity psi hpsi)))
    (j : Fin (Module.finrank Complex K)) :
    rightTensorCoefficients b psi j ∈ C.carrier := by sorry
