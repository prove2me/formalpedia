-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_selectedReferenceMarginal_pureDensity_toOperator_sum
-- name    : QEC.Semantics.QuditSubsystem.selectedReferenceMarginal_pureDensity_toOperator_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:20:22.517193+00:00
-- url     : https://prove2.me/theorems/dc184f2a-4be8-4374-8442-f482af05ff47
-- title:
--   Qudit Subsystem: selected Reference Marginal pure Density to Operator sum
-- statement:
--   The Qudit Subsystem construction uses the selected Reference Marginal pure Density to Operator sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L1213-L1241
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L1213-L1241

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

theorem QEC.Semantics.QuditSubsystem.selectedReferenceMarginal_pureDensity_toOperator_sum (S : QuditSubsystem q)
    (Ref : Type u) [NormedAddCommGroup Ref] [InnerProductSpace Complex Ref]
    [FiniteQuantumSystem Ref]
    (b : OrthonormalBasis (Fin (Module.finrank Complex Ref)) Complex Ref)
    (psi : CompositeSystem (Qudit.QuditRegister q) Ref) (hpsi : ‖psi‖ ^ 2 = 1) :
    (S.selectedReferenceMarginal Ref (pureDensity psi hpsi)).toOperator =
      ∑ i, ∑ j,
        TensorProduct.map
          (S.selectedPartialTraceFromRegister
            (InnerProductSpace.rankOne Complex (rightTensorCoefficients b psi i)
              (rightTensorCoefficients b psi j)).toLinearMap)
          (InnerProductSpace.rankOne Complex (b i) (b j)).toLinearMap := by sorry
