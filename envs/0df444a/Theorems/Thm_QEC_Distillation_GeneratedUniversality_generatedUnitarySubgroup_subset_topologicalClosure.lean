-- Prove2me | Theorems.Thm_QEC_Distillation_GeneratedUniversality_generatedUnitarySubgroup_subset_topologicalClosure
-- name    : QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup_subset_topologicalClosure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T14:09:28.533485+00:00
-- url     : https://prove2.me/theorems/d098fcad-890f-450d-9033-8dbbee61018b
-- title:
--   Generated Universality: generated Unitary Subgroup subset topological Closure
-- statement:
--   Every generated unitary lies in the topological closure of its generated subgroup.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L176-L180
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Distillation/Universality/GeneratedUniversality.lean#L176-L180

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

theorem QEC.Distillation.GeneratedUniversality.generatedUnitarySubgroup_subset_topologicalClosure {n : Type u}
    [Fintype n] [DecidableEq n] (generators : Set (UnitaryGate n)) :
    (generatedUnitarySubgroup generators : Set (UnitaryGate n)) ⊆
      generatedUnitaryTopologicalClosure generators := by sorry
