-- Prove2me | Theorems.Thm_PI_GGConvScalarW_superdiag_mul
-- name    : PI.GGConvScalarW.superdiag_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:30:54.724338+00:00
-- url     : https://prove2.me/theorems/fadfa703-c618-5f5b-8260-99a3cdb3af35
-- title:
--   GGConv Scalar W: superdiag mul
-- statement:
--   The GGConv Scalar W construction uses the superdiag mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L37-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L37-L61

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

theorem PI.GGConvScalarW.superdiag_mul {A B : Matrix (Fin k) (Fin k) F} (hA : IsUTm A) (hB : IsUTm B) :
    superdiag k (A * B) = superdiag k A + superdiag k B := by sorry
