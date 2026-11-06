-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_erasureRecovery_implies_selectedReferenceMarginal_factorizes
-- name    : QEC.Semantics.QuditSubsystem.erasureRecovery_implies_selectedReferenceMarginal_factorizes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:43:22.847084+00:00
-- url     : https://prove2.me/theorems/489c4004-4b82-42a6-9e43-9eed325901cd
-- title:
--   Qudit Subsystem: erasure Recovery implies selected Reference Marginal factorizes
-- statement:
--   Exact recovery from concrete finite qudit erasure forces the selected
--   subsystem of every finite purification to factor from its arbitrary reference.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L1433-L1504
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L1433-L1504

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

theorem QEC.Semantics.QuditSubsystem.erasureRecovery_implies_selectedReferenceMarginal_factorizes
    (S : QuditSubsystem q) (C : QuantumCode (Qudit.QuditRegister q))
    (recovery : QuantumChannel S.complementSystem (Qudit.QuditRegister q))
    (hcorrect : Correctable (Qudit.QuditRegister q) S.complementSystem C
      S.erasureChannelFromRegister recovery)
    (rho : DensityOperator (Qudit.QuditRegister q))
    (hsupported : DensityOperator.SupportedOn C rho)
    (Ref : Type u) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [FiniteQuantumSystem Ref]
    (purification : DensityOperator.FinitePurification rho Ref) :
    S.selectedReferenceMarginal Ref
      (pureDensity purification.vector purification.normSq_one) =
      tensorDensity (S.selectedPartialTraceFromRegister.mapDensity rho)
        (leftMarginal (pureDensity purification.vector purification.normSq_one)) := by sorry
