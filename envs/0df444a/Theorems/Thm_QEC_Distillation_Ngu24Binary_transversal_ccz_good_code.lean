-- Prove2me | Theorems.Thm_QEC_Distillation_Ngu24Binary_transversal_ccz_good_code
-- name    : QEC.Distillation.Ngu24Binary.transversal_ccz_good_code
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-09T12:41:59.283606+00:00
-- url     : https://prove2.me/theorems/b55b5bed-0d4a-4bc7-85c8-fe8599d1a654
-- title:
--   Ngu24 Binary: transversal ccz good code
-- statement:
--   The source-backed binary CSS family, with two-sided linear bounds, actual
--   quantum distance, disjoint inverse-permuted triples of positive density,
--   and full tensor-encoding CCZ intertwining [Ngu24, Main result and Step 3].
--
--   All families and operators in the statement are the concrete constructions
--   above; no family, distance, gate action, or parameter conclusion is assumed.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/TransversalCCZFamily.lean#L25-L66
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/TransversalCCZFamily.lean#L25-L66

import Definitions.Def_QEC_Distillation_MultiplicativeQuditProtocol_BinaryFamily
import Definitions.Def_QEC_Results_Distillation_TransversalCCZFamily
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Ngu24Binary
open Coding Semantics Ngu24MultiplicativeCSS
open Coding.AlgebraicGeometry.F256GarciaStichtenoth
open Filter

theorem QEC.Distillation.Ngu24Binary.transversal_ccz_good_code :
    Tendsto binaryLength atTop atTop ∧
    ∀ i : Nat,
      binaryLength i = 512 * (f256GarciaStichtenothLength i - f256MultiplicationLogicalCount i) ∧
      binaryLength i = Fintype.card ((f256SourceInput i).PivotComplement × Fin 512) ∧
      f256MultiplicationLogicalCount i = f256GarciaStichtenothLength i / 10 ∧
      (binaryEncodedCode i).code = (binaryCSSCode i).stabilizer.code ∧
      (binaryCSSCode i).stabilizer.code.dimension = 2 ^ f256MultiplicationLogicalCount i ∧
      QuditSubsystem.BPTMeasurementDistance (binaryCSSCode i).stabilizer.code (binaryDistance i) ∧
      (¬ QuditSubsystem.BPTMeasurementDistance (binaryCSSCode i).stabilizer.code (binaryDistance i + 1)) ∧
      (f256GarciaStichtenothLength i : ℚ) / 5 - f256MultiplicationLogicalCount i ≤ binaryDistance i ∧
      ((binaryLength i : ℚ) / 10240 ≤ f256MultiplicationLogicalCount i ∧
        (f256MultiplicationLogicalCount i : ℚ) ≤ binaryLength i) ∧
      ((binaryLength i : ℚ) / 5120 ≤ binaryDistance i ∧ (binaryDistance i : ℚ) ≤ binaryLength i) ∧
      (binaryLength i : ℚ) / 512 ≤ (binarySelectedSites (f256SourceInput i).PivotComplement).card ∧
      (∀ x, (binaryTripleSupport (f256SourceInput i).PivotComplement x).card = 3) ∧
      (∀ x y, x ≠ y → Disjoint
        (binaryTripleSupport (f256SourceInput i).PivotComplement x)
        (binaryTripleSupport (f256SourceInput i).PivotComplement y)) ∧
      (binaryPhysicalFactorization (J := (f256SourceInput i).PivotComplement)).factorCount =
        (binarySelectedSites (f256SourceInput i).PivotComplement).card ∧
      (∀ phi : Qubit.QubitRegister (Fin (f256MultiplicationLogicalCount i)),
        binaryEncodingIsometry i phi =
          mfeFromSelfDualIsometry (f256SourceInput i).PivotComplement
            (selfDualIsometry (f256SourceInput i).PivotComplement
              ((f256SourceInput i).encodingLinearMap
                (logicalIsometry (Fin (f256MultiplicationLogicalCount i)) phi)))) ∧
      ∀ psi : TaggedThreeCopyRegister (ZMod 2) (Fin (f256MultiplicationLogicalCount i)),
        binaryPhysicalCCZ
            (taggedTensorCube (ZMod 2) (Fin (f256MultiplicationLogicalCount i))
              ((f256SourceInput i).PivotComplement × Fin 512) (binaryEncodingIsometry i).toLinearMap psi) =
          taggedTensorCube (ZMod 2) (Fin (f256MultiplicationLogicalCount i))
            ((f256SourceInput i).PivotComplement × Fin 512) (binaryEncodingIsometry i).toLinearMap
              (binaryLogicalCCZ psi) := by sorry
