-- Prove2me | Theorems.Thm_QEC_Coding_AlgebraicGeometry_agEvaluation_le_dual_of_residue
-- name    : QEC.Coding.AlgebraicGeometry.agEvaluation_le_dual_of_residue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T19:20:49.03736+00:00
-- url     : https://prove2.me/theorems/558f4116-1f06-4b34-bbb7-bbf96ed3a882
-- title:
--   Algebraic Geometry: ag Evaluation le dual of residue
-- statement:
--   Divisor domination and the actual unit residues give code orthogonality.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/ResiduePairing.lean#L150-L167
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/AlgebraicGeometry/Codes/ResiduePairing.lean#L150-L167

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

theorem QEC.Coding.AlgebraicGeometry.agEvaluation_le_dual_of_residue
    (G H : Divisor (GlobalPlace k F)) (Q : ι → RationalPlace k F)
    (hQ : Function.Injective fun j => (Q j).place)
    (hG : ∀ j, G (Q j).place = 0) (hH : ∀ j, H (Q j).place = 0)
    (eta : Differential k F) (heta : eta ≠ 0)
    (etaAt : ∀ j, Differential.simplePoleDifferentialLattice (Q j).place)
    (hAt : ∀ j, (etaAt j : Differential k F) = eta)
    (hres : ∀ j, Differential.simplePoleResidue (Q j).place (etaAt j) = 1)
    (hGH : G + H ≤ differentialDivisor eta heta + evaluationDivisor Q) :
    (agEvaluationCode H Q hH).carrier ≤ (agEvaluationCode G Q hG).dual.carrier := by sorry
