-- Prove2me | Theorems.Thm_QEC_Semantics_FiniteInstrument_branchOperator_smul
-- name    : QEC.Semantics.FiniteInstrument.branchOperator_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:31:11.359683+00:00
-- url     : https://prove2.me/theorems/c1057b5f-a09b-471c-ab13-327b26e84ffa
-- title:
--   Finite Instrument: branch Operator smul
-- statement:
--   An observed branch preserves complex scalar multiplication of an
--   unnormalized input operator.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Branches/BranchOperatorLinear.lean#L51-L61
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/Instruments/Branches/BranchOperatorLinear.lean#L51-L61

import Definitions.Def_QEC_Semantics_Instruments_Core
import Definitions.Def_QEC_Semantics_Instruments_Branches_BranchOperatorLinear
set_option autoImplicit false
universe u v w x
open QEC
open QEC.Semantics
open Classical
open scoped BigOperators
noncomputable section
open QEC.Semantics.FiniteInstrument
variable {kappa : Type v} [Fintype kappa]
variable {Omega : Type w} [Fintype Omega]
variable {H K : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace Complex H] [FiniteQuantumSystem H]
variable [NormedAddCommGroup K] [InnerProductSpace Complex K] [FiniteQuantumSystem K]

theorem QEC.Semantics.FiniteInstrument.branchOperator_smul (I : FiniteInstrument kappa Omega H K)
    (outcome : Omega) (c : Complex) (A : Operator H) :
    I.branchOperator outcome (c • A) =
      c • I.branchOperator outcome A := by sorry
