-- Prove2me | Theorems.Thm_PI_GGConvScalarW_superdiag_sgn_conj
-- name    : PI.GGConvScalarW.superdiag_sgn_conj
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T05:31:02.2721+00:00
-- url     : https://prove2.me/theorems/d03759c7-62bf-434d-84ba-f83a9d37e84d
-- title:
--   GGConv Scalar W: superdiag sgn conj
-- statement:
--   The GGConv Scalar W construction uses the superdiag sgn conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L142-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L142-L154

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

theorem PI.GGConvScalarW.superdiag_sgn_conj (A : Matrix (Fin k) (Fin k) F) :
    superdiag k (sgnM (F := F) k * A * sgnM (F := F) k) = - superdiag k A := by sorry
