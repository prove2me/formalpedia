-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Protocol_rawMarginalErrorWeight_eq_evenFamilyWeightSum
-- name    : QEC.Distillation.Triorthogonal.BH12Protocol.rawMarginalErrorWeight_eq_evenFamilyWeightSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T17:07:10.350213+00:00
-- url     : https://prove2.me/theorems/d478f557-3115-40c6-a36d-eef35803c501
-- title:
--   BH12 Protocol: raw Marginal Error Weight eq even Family Weight Sum
-- statement:
--   Subtracting the actual zero-marginal extension dual mass from success and
--   using the two #754 enumerators gives the exact raw output-error polynomial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2410-L2423
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Protocol.lean#L2410-L2423

import Definitions.Def_QEC_Distillation_Triorthogonal_EvenFamily
import Definitions.Def_QEC_Distillation_Triorthogonal_NoisyInjection
import Definitions.Def_QEC_Coding_Stabilizer_JointMeasurement
import Definitions.Def_QEC_Semantics_Core_Subsystem
import Definitions.Def_QEC_Semantics_Entropy_Purification
import Definitions.Def_QEC_Distillation_Triorthogonal_Protocol
set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.Triorthogonal
open QEC.Distillation.Triorthogonal.BH12Protocol
open Semantics
open Coding
open Coding.PauliSymplectic
open BH12EvenFamily
open BH12NoisyInjection
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
universe u

theorem QEC.Distillation.Triorthogonal.BH12Protocol.rawMarginalErrorWeight_eq_evenFamilyWeightSum (q : Nat)
    (p : ErrorParameter) (a : OddRow q) :
    rawMarginalErrorWeight q p a =
      (16 : ℝ)⁻¹ *
        (1 + (1 - 2 * p.rate) ^ 8 +
          6 * (1 - 2 * p.rate) ^ (4 + 4 * q) -
          2 * (1 - 2 * p.rate) ^ 7 -
          6 * (1 - 2 * p.rate) ^ (3 + 4 * q)) := by sorry
