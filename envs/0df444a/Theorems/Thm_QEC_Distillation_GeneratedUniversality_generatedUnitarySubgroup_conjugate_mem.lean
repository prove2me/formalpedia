-- Prove2me | Theorems.Thm_QEC_Distillation_GeneratedUniversality_generatedUnitarySubgroup_conjugate_mem
-- name    : QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup_conjugate_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:09:29.236206+00:00
-- url     : https://prove2.me/theorems/6f913b91-04c6-42ae-af8c-c5a11c90bfe5
-- title:
--   Generated Universality: generated Unitary Subgroup conjugate mem
-- statement:
--   A generated subgroup is closed under conjugation by its generated unitaries.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L166-L173
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L166-L173

import Definitions.Def_QEC_Semantics_Core_Definitions
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.UnitaryGroup
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
set_option autoImplicit false
noncomputable section
universe u
open QEC
open QEC.Distillation
open QEC.Distillation.GeneratedUniversality
open Semantics
open scoped Matrix.Norms.Elementwise

theorem QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup_conjugate_mem {n : Type u} [Fintype n] [DecidableEq n]
    (generators : Set (UnitaryGate n)) {U V : UnitaryGate n}
    (hU : U ∈ generatedUnitarySubgroup generators)
    (hV : V ∈ generatedUnitarySubgroup generators) :
    U * V * U⁻¹ ∈ generatedUnitarySubgroup generators := by sorry
