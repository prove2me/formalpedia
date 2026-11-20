-- Prove2me | Theorems.Thm_QEC_Distillation_Why24ConstantOverhead_why24_constant_overhead_distillation
-- name    : QEC.Distillation.Why24ConstantOverhead.why24_constant_overhead_distillation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T09:51:00.395472+00:00
-- url     : https://prove2.me/theorems/b6b92d78-e85f-4650-8b4d-cfd62628b6b1
-- title:
--   Why24 Constant Overhead: why24 constant overhead distillation
-- statement:
--   WHY24's constant-overhead theorem for the actual F1024 family and the
--   actual correlated local-stochastic one-round preparation.  The same theorem
--   records the computed finite T/CCZ conversions and charges the returned
--   catalyst its positive BH12 successful-output cost before amortization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/ConstantOverhead.lean#L372-L492
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/ConstantOverhead.lean#L372-L492

import Mathlib.Data.Nat.Choose.Bounds
import Definitions.Def_QEC_Distillation_Universality_AdaptiveIdealClifford
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_OneRound
import Definitions.Def_QEC_Distillation_ConstantOverheadProtocol_ResourceConversions
import Definitions.Def_QEC_Results_Distillation_ConstantOverhead
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Why24ConstantOverhead
open Filter Topology
open Semantics
open Why24AGFamily Why24OneRoundProtocol
open QEC.Coding.AlgebraicGeometry.GarciaStichtenothParameters
open Triorthogonal.BH12Concatenation
open Triorthogonal.BH12EvenFamily
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12Protocol

theorem QEC.Distillation.Why24ConstantOverhead.why24_constant_overhead_distillation :
    exists threshold Omega : Real,
      0 < threshold ∧
      0 < Omega ∧
      (forall epsilon : Real, 0 < epsilon ->
        forall physicalRate : Real, 0 <= physicalRate ->
          physicalRate < threshold ->
            exists firstIndex : Nat,
              forall index : Nat, firstIndex <= index ->
                forall preparation : Why24LocalStochasticPreparation
                    (Fin (why24OneRoundInputCount index))
                    (why24IdealCCZRegisterDensity
                      (why24OneRoundInputCount index)),
                  preparation.rate <= physicalRate ->
                    let protocol :=
                      why24OneRoundMagicStateDistillationProtocol index preparation
                    protocol.run = why24OneRoundRun index preparation ∧
                      protocol.inputErrorModel = InputErrorModel.localStochastic
                        (why24LocalStochasticInputErrorModel preparation) ∧
                      protocol.behavior = .activeCorrection (QuantumChannel.id _) ∧
                      protocol.run.resourceCount = 70 * f1024Why24OddLength index ∧
                      why24OneRoundOutputCount index =
                        f1024Why24OddDimension index ∧
                      protocol.run.successProbability = 1 ∧
                      protocol.successfulOutputError <=
                        why24GeometricErrorEnvelope index ∧
                      protocol.successfulOutputError <= epsilon ∧
                      (why24OneRoundInputCount index : Real) /
                        why24OneRoundOutputCount index <= Omega) ∧
      (forall index batch : Nat, 0 < batch ->
        ((4 * batch * why24OneRoundInputCount index : Nat) : Real) /
            (2 * batch * why24OneRoundOutputCount index) <= 3360) ∧
      (forall batch : Nat,
        why24RunConversionProgram (why24FourTToCCZBatch batch)
            { tCount := 4 * batch
              cczCount := 0 } =
            some
              { tCount := 0
                cczCount := batch } ∧
          why24RunConversionProgram (why24CCZCatalyticTBatch batch)
            { tCount := 1
              cczCount := batch } =
            some
              { tCount := 2 * batch + 1
                cczCount := 0 }) ∧
      0 < why24CatalystSeedCost ∧
      (exists seedParameter : ErrorParameter,
        seedParameter.rate = 1 / 200 ∧
        exists hsmall :
            (bh12InputCount 1 : Real) * seedParameter.rate <= 1 / 4,
          exists hhalf : seedParameter.rate <= 1 / 2,
            exists hstrong :
                quadraticCoefficient 1 * seedParameter.rate <= 1 / 2,
              exists schedule : BH12PathScheduleIndex 1,
                why24CatalystSeedCost =
                    bh12PathScheduleTypedSuccessfulOutputCost 1 seedParameter
                      hsmall hhalf hstrong schedule ∧
                  DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
                    (bh12PathScheduleInputSlots 1) (bh12PathScheduleOutputSlots 1)
                    (bh12PathScheduleTargetError 1 seedParameter)
                    (fun schedule =>
                      (bh12PathParameter 1 seedParameter
                        schedule.depth schedule.path).rate)
                    (bh12PathScheduleTypedYieldFactor 1 seedParameter
                      hsmall hhalf hstrong)
                    (bh12BlockExponent 1)
                    (bh12QuadraticEnvelopeCostCoefficient 1 seedParameter) ∧
                  (forall seedEpsilon : Real, 0 < seedEpsilon ->
                    exists depth : Nat, forall path : depthOutputPath 1 depth,
                      0 < rawSuccessMass 1
                          (bh12PathParameter 1 seedParameter depth path) ∧
                        0 < (bh12PathRun 1 seedParameter depth path).successProbability ∧
                          (forall port : OddRow 1,
                            bh12PathSelectedPortTransportedDensity 1 seedParameter
                                depth path port =
                              OneQubit.diagonalAResource
                                (bh12TotalNextParameter 1
                                  (bh12PathParameter 1 seedParameter depth path)
                                  port)) ∧
                            (bh12PathParameter 1 seedParameter depth path).rate <=
                              seedEpsilon)) ∧
      Tendsto why24CatalystSeedCostPerFreshOutput atTop (nhds 0) := by sorry
