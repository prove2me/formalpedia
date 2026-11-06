-- Prove2me | Theorems.Thm_QEC_Semantics_QuditSubsystem_prepareSelected_pureDensity_apply
-- name    : QEC.Semantics.QuditSubsystem.prepareSelected_pureDensity_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T13:58:53.597288+00:00
-- url     : https://prove2.me/theorems/ebd5ae44-fb18-49b2-b021-402e26b307fe
-- title:
--   Qudit Subsystem: prepare Selected pure Density apply
-- statement:
--   The Qudit Subsystem construction uses the prepare Selected pure Density apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L1404-L1410
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Semantics/ErrorCorrection/ReferenceDecoupling.lean#L1404-L1410

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

theorem QEC.Semantics.QuditSubsystem.prepareSelected_pureDensity_apply (S : QuditSubsystem q)
    (u : S.selectedSystem) (hu : ‖u‖ ^ 2 = 1) (A : Operator S.complementSystem) :
    S.prepareSelected (pureDensity u hu) A =
      S.registerFactorization.symm.conjOperator
        (TensorProduct.map (InnerProductSpace.rankOne Complex u u).toLinearMap A) := by sorry
