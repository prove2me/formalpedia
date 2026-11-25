-- Prove2me | Theorems.Thm_PI_GGConvScalarW_isUTm_sgn_conj
-- name    : PI.GGConvScalarW.isUTm_sgn_conj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:30:10.836113+00:00
-- url     : https://prove2.me/theorems/e1754f0b-69bc-5be2-8639-5d15253cff81
-- title:
--   GGConv Scalar W: is UTm sgn conj
-- statement:
--   The GGConv Scalar W construction uses the is UTm sgn conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L137-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L137-L140

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

theorem PI.GGConvScalarW.isUTm_sgn_conj {A : Matrix (Fin k) (Fin k) F} (h : IsUTm A) : IsUTm (sgnM (F := F) k * A * sgnM (F := F) k) := by sorry
