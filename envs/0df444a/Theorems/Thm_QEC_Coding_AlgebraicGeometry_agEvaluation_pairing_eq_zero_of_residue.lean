-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_pairing_eq_zero_of_residue
-- name    : QEC.Coding.AlgebraicGeometry.agEvaluation_pairing_eq_zero_of_residue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:20:49.581385+00:00
-- url     : https://prove2.me/theorems/d6d620d5-6869-480a-ab67-45c5911b8113
-- title:
--   Algebraic Geometry: ag Evaluation pairing eq zero of residue
-- statement:
--   Pairing vanishes by applying the global residue theorem to `xy eta`.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/ResiduePairing.lean#L38-L147
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/ResiduePairing.lean#L38-L147

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_Code
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Residues_Global_FunctionFieldGlobalResidue
import Definitions.Def_QEC_Coding_AlgebraicGeometry_RiemannRoch_PrincipalShift
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Codes_ResiduePairing
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry
open scoped BigOperators
open FunctionFieldDifferential
noncomputable section
variable (k F : Type*) [Field k] [Fintype k] [Field F]
variable [π : Algebra (Polynomial k) F] [ρ : Algebra (RatFunc k) F]
variable [τ : IsScalarTower (Polynomial k) (RatFunc k) F]
variable [φ : _root_.FunctionField k F] [s : Algebra.IsSeparable (RatFunc k) F]
attribute [local instance] QEC.Coding.AlgebraicGeometry.residuePairingConstantAlgebra
attribute [local instance] QEC.Coding.AlgebraicGeometry.residuePairingConstantTower
variable {ι : Type*} [Fintype ι]

theorem QEC.Coding.AlgebraicGeometry.agEvaluation_pairing_eq_zero_of_residue
    (G H : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (hH : ∀ j, H (Q j).place = 0)
    (eta : Differential k F) (heta : eta ≠ 0)
    (etaAt : ∀ j, Differential.simplePoleDifferentialLattice (Q j).place)
    (hAt : ∀ j, (etaAt j : Differential k F) = eta)
    (hres : ∀ j, Differential.simplePoleResidue (Q j).place (etaAt j) = 1)
    (hGH : G + H ≤ differentialDivisor eta heta + evaluationDivisor Q)
    (x : GlobalPlace.riemannRochSubmodule G)
    (y : GlobalPlace.riemannRochSubmodule H) :
    wordPairing (agEvaluationLinearMap G Q hG x) (agEvaluationLinearMap H Q hH y) = 0 := by sorry
