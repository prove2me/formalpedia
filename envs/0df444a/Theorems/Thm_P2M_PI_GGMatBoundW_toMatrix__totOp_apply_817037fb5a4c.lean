-- Prove2me | Theorems.Thm_P2M_PI_GGMatBoundW_toMatrix__totOp_apply_817037fb5a4c
-- name    : P2M_PI_GGMatBoundW_toMatrix__totOp_apply_817037fb5a4c
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:11:51.578538+00:00
-- url     : https://prove2.me/theorems/8bb43b44-bf42-4a9b-a862-7aa29bee7f75
-- title:
--   P2 M PI GGMat Bound W to Matrix  tot Op apply 817037fb5a4c: P2 M PI GGMat Bound W to Matrix  tot Op apply 817037fb5a4c
-- statement:
--   The P2 M PI GGMat Bound W to Matrix  tot Op apply 817037fb5a4c construction uses the P2 M PI GGMat Bound W to Matrix  tot Op apply 817037fb5a4c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/MatrixCoefficientEquation.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/MatrixCoefficientEquation.lean#L74-L79

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_GammaMatrixInverse
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_MatrixCoefficientEquation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open scoped ComplexConjugate
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {ι : Type} [Fintype ι] {Fq : ι → Type} [∀ v, Field (Fq v)] [∀ v, Fintype (Fq v)] {k : ℕ}

theorem P2M_PI_GGMatBoundW_toMatrix__totOp_apply_817037fb5a4c (ψ : ∀ v, AddChar (Fq v) ℂ) (X : Type) [Fintype X]
    [MulAction (∀ v, GL (Fin k) (Fq v))ᵐᵒᵖ X] (i j : X) :
    LinearMap.toMatrix' (totOp ψ (permRep (∀ v, GL (Fin k) (Fq v)) X)) i j =
      ∑ x : (∀ v, GL (Fin k) (Fq v)), if MulOpposite.op x • i = j then gamProd ψ x else 0 := by sorry

alias «PI».«GGMatBoundW».«toMatrix'_totOp_apply» := P2M_PI_GGMatBoundW_toMatrix__totOp_apply_817037fb5a4c
