-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_UsCost_DA_hasDerivAt_block_matrix_three
-- name    : PI.UnitaryGroupMassFormula.UsCost.DA.hasDerivAt_block_matrix_three
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T05:42:35.201105+00:00
-- url     : https://prove2.me/theorems/12c3bc81-11fb-485a-b396-f3f1a2bb0d26
-- title:
--   DA: has Deriv At block matrix three
-- statement:
--   The DA construction uses the has Deriv At block matrix three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivA.lean#L112-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnipotentCost/DerivA.lean#L112-L134

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_LetterSize
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCost_DerivA
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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UsCost PI.UnitaryGroupMassFormula.UsCost.DA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {t : ℝ}

theorem PI.UnitaryGroupMassFormula.UsCost.DA.hasDerivAt_block_matrix_three {k j ρ : ℕ} {A11 : ℝ → Matrix (Fin j) (Fin j) ℂ} {A12 : ℝ → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {A13 : ℝ → Matrix (Fin j) (Fin j) ℂ} {A21 : ℝ → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A22 : ℝ → B.Mat k ρ}
    {A23 : ℝ → Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {A31 : ℝ → Matrix (Fin j) (Fin j) ℂ}
    {A32 : ℝ → Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {A33 : ℝ → Matrix (Fin j) (Fin j) ℂ}
    {ToralGalois : Matrix (Fin j) (Fin j) ℂ} {cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ}
    {B13 : Matrix (Fin j) (Fin j) ℂ} {B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {B22 : B.Mat k ρ}
    {B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ} {B31 : Matrix (Fin j) (Fin j) ℂ}
    {B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ} {B33 : Matrix (Fin j) (Fin j) ℂ}
    (h11 : HasDerivAt A11 ToralGalois t) (h12 : HasDerivAt A12 cocyclesToWachVectorsExponent t) (h13 : HasDerivAt A13 B13 t)
    (h21 : HasDerivAt A21 B21 t) (h22 : HasDerivAt A22 B22 t) (h23 : HasDerivAt A23 B23 t)
    (h31 : HasDerivAt A31 B31 t) (h32 : HasDerivAt A32 B32 t) (h33 : HasDerivAt A33 B33 t) :
    HasDerivAt (fun y => blk3 (A11 y) (A12 y) (A13 y) (A21 y) (A22 y) (A23 y) (A31 y) (A32 y) (A33 y))
      (blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33) t := by sorry
