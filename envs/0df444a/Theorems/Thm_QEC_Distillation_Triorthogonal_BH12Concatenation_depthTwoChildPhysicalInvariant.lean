-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_depthTwoChildPhysicalInvariant
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.depthTwoChildPhysicalInvariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:35:27.675427+00:00
-- url     : https://prove2.me/theorems/6c99c796-2ae2-47b1-9b9b-b58499e893ec
-- title:
--   BH12 Concatenation: depth Two Child Physical Invariant
-- statement:
--   Two physical BH12 levels assembled from fresh parent outputs: the child
--   run succeeds, has its exact selected-port diagonal resource, and obeys the
--   twice-applied quadratic error bound.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1410-L1473
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1410-L1473

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
import Definitions.Def_QEC_Distillation_Core_DependentBatch
import Definitions.Def_QEC_Distillation_Core_Overhead
import Definitions.Def_QEC_Distillation_Triorthogonal_Concatenation
set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.Triorthogonal QEC.Distillation.Triorthogonal.BH12Concatenation
open Semantics
open BH12EvenFamily
open BH12NoisyInjection
open BH12Protocol
open Filter Topology

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.depthTwoChildPhysicalInvariant (q : Nat) (p : ErrorParameter)
    (firstPort secondPort : OddRow q)
    (hsmall : (bh12InputCount q : ℝ) * p.rate ≤ 1 / 4)
    (hhalf : p.rate ≤ 1 / 2)
    (hquadraticSmall : quadraticCoefficient q * p.rate ≤ 1) :
    ∃ hfirst : 0 < rawSuccessMass q p,
      ∃ hsecond : 0 < rawSuccessMass q
          (bh12DecodedMarginalErrorParameter q p hfirst firstPort),
        0 < (depthTwoChildRun q p firstPort).successProbability ∧
          depthTwoChildSelectedPortTransportedDensity q p firstPort secondPort =
            OneQubit.diagonalAResource
              (bh12DecodedMarginalErrorParameter q
                (bh12DecodedMarginalErrorParameter q p hfirst firstPort)
                hsecond secondPort) ∧
          (bh12DecodedMarginalErrorParameter q
            (bh12DecodedMarginalErrorParameter q p hfirst firstPort)
            hsecond secondPort).rate ≤
              quadraticCoefficient q ^ 3 * p.rate ^ 4 := by sorry
