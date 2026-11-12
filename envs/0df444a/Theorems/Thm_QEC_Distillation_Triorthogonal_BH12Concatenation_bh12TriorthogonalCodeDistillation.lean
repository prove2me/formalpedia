-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12TriorthogonalCodeDistillation
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12TriorthogonalCodeDistillation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:44:50.827235+00:00
-- url     : https://prove2.me/theorems/1256abc9-700d-46fc-bf62-e7d617a328e8
-- title:
--   BH12 Concatenation: bh12 Triorthogonal Code Distillation
-- statement:
--   The complete source-backed BH12 public realization for one positive
--   family index.  Every component is derived from the concrete #753--#756
--   construction: the explicit CSS family, its corrected transversal action, the
--   independent diagonal physical input and syndrome-postselected run, the
--   level-indexed fresh-parent expected-yield accounting, and the exact finite
--   block exponent.  The multi-level predicate is intentionally additive rather
--   than an invalid fixed-register `DistillationProtocolFamily`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/TriorthogonalDistillation.lean#L24-L95
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Results/Distillation/TriorthogonalDistillation.lean#L24-L95

import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
import Definitions.Def_QEC_Results_Distillation_TriorthogonalDistillation
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily BH12NoisyInjection BH12Protocol
open Filter Topology

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12TriorthogonalCodeDistillation (q : Nat) (p : ErrorParameter)
    (hq : 0 < q) (hp : 0 < p.rate)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hstrong : quadraticCoefficient q * p.rate ≤ 1 / 2) :
    bh12InputCount q = 3 * bh12OutputCount q + 8 ∧
      Fintype.card (OddRow q) = bh12OutputCount q ∧
        Coding.PureZLogicalMinimumDistance (family q).evenCode (family q).rowCode.dual 2 ∧
          ((family q).encodedCode (isTriorthogonal q)).ImplementsLogicalGate
              (family q).correctedAllSiteT (allSiteT (Index := OddRow q)) ∧
            (InputErrorModel.independent (bh12IndependentInputModel q p)).Permits
                (noisyResources q p) ∧
              (∀ port : OddRow q, ∃ hsuccess : 0 < rawSuccessMass q p,
                0 < (bh12ActualRun q p).successProbability ∧
                  bh12SelectedPortTransportedDensity q p port =
                    OneQubit.diagonalAResource
                      (bh12DecodedMarginalErrorParameter q p hsuccess port) ∧
                  (bh12DecodedMarginalErrorParameter q p hsuccess port).rate ≤
                    quadraticCoefficient q * p.rate ^ 2) ∧
                DependentBatch.physicalPolylogarithmicExpectedYieldOverhead
                  (bh12PathScheduleInputSlots q) (bh12PathScheduleOutputSlots q)
                  (bh12PathScheduleTargetError q p)
                  (fun index =>
                    (bh12PathParameter q p index.depth index.path).rate)
                  (bh12PathScheduleTypedYieldFactor q p hsmall hhalf hstrong)
                  (bh12BlockExponent q) (bh12QuadraticEnvelopeCostCoefficient q p) ∧
                  (∀ path : depthOutputPath q 1,
                    bh12PathTypedSuccessfulOutputCost q p hsmall hhalf hstrong 1 path =
                      (bh12OneLevelProtocolFamily q p hhalf).successfulOutputCost (path 0)) ∧
                    (∀ epsilon : ℝ, 0 < epsilon →
                      ∃ z : Nat, ∀ path : depthOutputPath q z,
                        0 < rawSuccessMass q (bh12PathParameter q p z path) ∧
                          0 < (bh12PathRun q p z path).successProbability ∧
                            (∀ port : OddRow q,
                              bh12PathSelectedPortTransportedDensity q p z path port =
                                OneQubit.diagonalAResource
                                  (bh12TotalNextParameter q
                                    (bh12PathParameter q p z path) port)) ∧
                              (bh12PathParameter q p z path).rate ≤ epsilon) ∧
                      bh12BlockExponent q =
                        Real.log (((3 * bh12OutputCount q + 8 : Nat) : ℝ) /
                          (bh12OutputCount q : ℝ)) / Real.log 2 ∧
                        Tendsto (fun index : Nat => bh12BlockExponent (index + 1)) atTop
                          (𝓝 (Real.log 3 / Real.log 2)) ∧
                          bh12BlockExponent q ≠ Real.log 3 / Real.log 2 ∧
                            (∀ k : Nat, Even k → 0 < k →
                              ∃ index : Nat, 0 < index ∧ k = logicalCount index ∧
                                bh12BlockExponent index =
                                  Real.log (((3 * k + 8 : Nat) : ℝ) / (k : ℝ)) /
                                    Real.log 2 ∧
                                  Real.log 3 / Real.log 2 < bh12BlockExponent index) := by sorry
