-- Prove2me | Theorems.Thm_QEC_Distillation_Triorthogonal_BH12Concatenation_one_le_quadraticCoefficient
-- name    : QEC.Distillation.Triorthogonal.BH12Concatenation.one_le_quadraticCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-11T22:31:36.510641+00:00
-- url     : https://prove2.me/theorems/e85096b3-f59c-4c9c-acf8-953279c4718f
-- title:
--   BH12 Concatenation: one le quadratic Coefficient
-- statement:
--   The BH12 quadratic coefficient is at least one.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1738-L1742
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Triorthogonal/Concatenation.lean#L1738-L1742

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

theorem QEC.Distillation.Triorthogonal.BH12Concatenation.one_le_quadraticCoefficient (q : Nat) : 1 ≤ quadraticCoefficient q := by sorry
