-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_mem_agEvaluation_sub_divisor_iff_shortened
-- name    : QEC.Coding.AlgebraicGeometry.mem_agEvaluation_sub_divisor_iff_shortened
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:08:06.216522+00:00
-- url     : https://prove2.me/theorems/fe3d9d57-9d7d-430e-8db0-77c06b25e07f
-- title:
--   Algebraic Geometry: mem ag Evaluation sub divisor iff shortened
-- statement:
--   A precise membership characterization of the AG shortened code.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/EvaluationShortening.lean#L33-L62
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/EvaluationShortening.lean#L33-L62

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationKernel
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_EvaluationShortening
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
noncomputable section
variable {k F ι J : Type*} [Field k] [Fintype k] [Field F] [Algebra k F]
variable [Fintype ι] [Fintype J]

theorem QEC.Coding.AlgebraicGeometry.mem_agEvaluation_sub_divisor_iff_shortened
    (G : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (p : J ↪ ι)
    [Fintype {j : ι // j ∉ Set.range p}]
    (w : Word k {j : ι // j ∉ Set.range p}) :
    w ∈ (agEvaluationCode (G - evaluationDivisor (fun a => Q (p a)))
      (fun j : {j : ι // j ∉ Set.range p} => Q j.val)
      (evaluationSupport_sub_of_not_range G Q hQ hG p)).carrier ↔
    ∃ x ∈ (agEvaluationCode G Q hG).carrier,
      (∀ a, x (p a) = 0) ∧ (fun j : {j : ι // j ∉ Set.range p} => x j.val) = w := by sorry
