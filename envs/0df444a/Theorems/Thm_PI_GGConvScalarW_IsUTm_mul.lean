-- Prove2me | Theorems.Thm_PI_GGConvScalarW_IsUTm_mul
-- name    : PI.GGConvScalarW.IsUTm.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:18:38.36092+00:00
-- url     : https://prove2.me/theorems/526db5d7-f8cd-4b27-bf73-6cbe06df32dc
-- title:
--   Is UTm: mul
-- statement:
--   The Is UTm construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L21-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L21-L35

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

theorem PI.GGConvScalarW.IsUTm.mul {A B : Matrix (Fin k) (Fin k) F} (hA : IsUTm A) (hB : IsUTm B) : IsUTm (A * B) := by sorry
