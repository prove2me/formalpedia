-- Prove2me | Theorems.Thm_P2M_PI_UnitaryGroupMassFormula_UsCost_permutationMatrix_eq_permMatrix__665b2f5dbc76
-- name    : P2M_PI_UnitaryGroupMassFormula_UsCost_permutationMatrix_eq_permMatrix__665b2f5dbc76
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:38:05.79638+00:00
-- url     : https://prove2.me/theorems/41f8bf83-430e-459c-84c7-1cd01ff86e4b
-- title:
--   P2 M PI Unitary Group Mass Formula Us Cost permutation Matrix eq perm Matrix  665b2f5dbc76: P2 M PI Unitary Group Mass Formula Us Cost permutation Matrix eq perm Matrix  665b2f5dbc76
-- statement:
--   The P2 M PI Unitary Group Mass Formula Us Cost permutation Matrix eq perm Matrix  665b2f5dbc76 construction uses the P2 M PI Unitary Group Mass Formula Us Cost permutation Matrix eq perm Matrix  665b2f5dbc76 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L124-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/Smooth.lean#L124-L126

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_Smooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} {x₀ : X}
variable {k p s ρ : ℕ} {σ : Equiv.Perm (Fin p)} {d : Fin p → ℂ}

theorem P2M_PI_UnitaryGroupMassFormula_UsCost_permutationMatrix_eq_permMatrix__665b2f5dbc76 (σ : Equiv.Perm (Fin p)) : wP σ = σ.permMatrix ℂ := by sorry

alias «PI».«UnitaryGroupMassFormula».«UsCost».«permutationMatrix_eq_permMatrix'» := P2M_PI_UnitaryGroupMassFormula_UsCost_permutationMatrix_eq_permMatrix__665b2f5dbc76
