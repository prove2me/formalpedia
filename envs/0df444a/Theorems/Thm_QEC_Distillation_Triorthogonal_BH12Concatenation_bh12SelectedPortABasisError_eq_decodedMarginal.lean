-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12SelectedPortABasisError_eq_decodedMarginal
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12SelectedPortABasisError_eq_decodedMarginal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:34:56.145743+00:00
-- url     : https://prove2.me/theorems/a2450887-ab82-4427-99d9-9dbf84dd30ff
-- title:
--   BH12 Concatenation: bh12 Selected Port ABasis Error eq decoded Marginal
-- statement:
--   #755's exact enumerator calculation identifies the selected port's actual
--   A-basis error diagnostic with its normalized marginal error.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1246-L1250
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1246-L1250

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12SelectedPortABasisError_eq_decodedMarginal (q : Nat)
    (p : ErrorParameter) (hsuccess : 0 < rawSuccessMass q p) (port : OddRow q) :
    bh12SelectedPortABasisError q p port = decodedMarginalError q p hsuccess port := by sorry
