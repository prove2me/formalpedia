-- Prove2me | Theorems.Thm_QEC_Distillation_GeneratedUniversality_generatedUnitarySubgroup_compose_mem
-- name    : QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup_compose_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:09:30.246207+00:00
-- url     : https://prove2.me/theorems/0cc0532d-a5c7-4cf8-9f48-81d876e93b02
-- title:
--   Generated Universality: generated Unitary Subgroup compose mem
-- statement:
--   A generated subgroup is closed under composition of generated unitaries.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L158-L163
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L158-L163

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

theorem QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup_compose_mem {n : Type u} [Fintype n] [DecidableEq n]
    (generators : Set (UnitaryGate n)) {U V : UnitaryGate n}
    (hU : U ∈ generatedUnitarySubgroup generators)
    (hV : V ∈ generatedUnitarySubgroup generators) :
    U * V ∈ generatedUnitarySubgroup generators := by sorry
