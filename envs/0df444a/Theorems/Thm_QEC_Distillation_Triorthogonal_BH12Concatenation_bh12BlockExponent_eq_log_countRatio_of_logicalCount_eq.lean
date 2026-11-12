-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_bh12BlockExponent_eq_log_countRatio_of_logicalCount_eq
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.bh12BlockExponent_eq_log_countRatio_of_logicalCount_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:27:11.596279+00:00
-- url     : https://prove2.me/theorems/5dfbfe64-37bd-4981-a426-513372dc8e71
-- title:
--   BH12 Concatenation: bh12 Block Exponent eq log count Ratio of logical Count eq
-- statement:
--   Reindexing by a positive even source count gives the exact real
--   logarithmic BH12 exponent; the denominator is never formed at `k = 0`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L127-L132
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L127-L132

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.bh12BlockExponent_eq_log_countRatio_of_logicalCount_eq {q k : Nat}
    (hq : 0 < q) (hk : k = logicalCount q) :
    bh12BlockExponent q =
      Real.log (((3 * k + 8 : Nat) : ℝ) / (k : ℝ)) / Real.log 2 := by sorry
