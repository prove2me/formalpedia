-- Prove2me | Theorems.Thm_PI_GGConvScalarW_sgn_conj_apply
-- name    : PI.GGConvScalarW.sgn_conj_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:28:31.038695+00:00
-- url     : https://prove2.me/theorems/ec687bd9-60ac-47e6-b9f9-dcbfd518c93e
-- title:
--   GGConv Scalar W: sgn conj apply
-- statement:
--   The GGConv Scalar W construction uses the sgn conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L132-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L132-L135

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GGMirabolic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ScalarConvolutionTrace_SuperdiagSgnConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
noncomputable section
open Classical
open PI PI.GGConvScalarW
open Formalism.L2.SG.GGMirabolic
variable {F : Type} [Field F] [Fintype F] {k : ℕ}

theorem PI.GGConvScalarW.sgn_conj_apply (A : Matrix (Fin k) (Fin k) F) (i j : Fin k) :
    (sgnM (F := F) k * A * sgnM (F := F) k) i j = (-1 : F) ^ (i : ℕ) * A i j * (-1 : F) ^ (j : ℕ) := by sorry
