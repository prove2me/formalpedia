-- Prove2me | Theorems.Thm_PI_GGMatBoundW_addChar_inv_eq_conj
-- name    : PI.GGMatBoundW.addChar_inv_eq_conj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:31:23.92603+00:00
-- url     : https://prove2.me/theorems/30b47735-fb0b-594b-8e4e-8ce2a2b89ab2
-- title:
--   GGMat Bound W: add Char inv eq conj
-- statement:
--   The GGMat Bound W construction uses the add Char inv eq conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/GammaMatrixInverse.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/GammaMatrixInverse.lean#L18-L20

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_GammaMatrixInverse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexConjugate
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic PI.GGConvScalarW

theorem PI.GGMatBoundW.addChar_inv_eq_conj {F : Type} [Field F] [Fintype F] (ψ₀ : AddChar F ℂ) (a : F) :
    (ψ₀ a)⁻¹ = conj (ψ₀ a) := by sorry
