-- Prove2me | Theorems.Thm_P2M_RH_PI_GGMatBoundW_gam_one_real_3ae542a281777c9f
-- name    : P2M_RH_PI_GGMatBoundW_gam_one_real_3ae542a281777c9f
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:15:48.065014+00:00
-- url     : https://prove2.me/theorems/edf70986-b74d-4aea-b4ff-2a6181a1c59e
-- title:
--   P2 M RH PI GGMat Bound W gam one real 3ae542a281777c9f: P2 M RH PI GGMat Bound W gam one real 3ae542a281777c9f
-- statement:
--   The P2 M RH PI GGMat Bound W gam one real 3ae542a281777c9f construction uses the P2 M RH PI GGMat Bound W gam one real 3ae542a281777c9f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/IrreducibleOfMinimal.lean#L77-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MatrixCoefficientBound/IrreducibleOfMinimal.lean#L77-L96

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_Reindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_RepresentationDimensionPos
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_PermRepApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MatrixCoefficientBound_IrreducibleOfMinimal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.GGMatBoundW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}

theorem P2M_RH_PI_GGMatBoundW_gam_one_real_3ae542a281777c9f (ψ₀ : AddChar F ℂ) :
    gam ψ₀ (1 : GL (Fin k) F) = (((Fintype.card (GL (Fin k) F) : ℝ) / (cardU F k : ℝ) : ℝ) : ℂ) := by sorry

alias «PI».«GGMatBoundW».«gam_one_real» := P2M_RH_PI_GGMatBoundW_gam_one_real_3ae542a281777c9f
