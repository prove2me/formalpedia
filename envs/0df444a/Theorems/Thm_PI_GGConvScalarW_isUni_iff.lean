-- Prove2me | Theorems.Thm_PI_GGConvScalarW_isUni_iff
-- name    : PI.GGConvScalarW.isUni_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:04:50.093214+00:00
-- url     : https://prove2.me/theorems/9d53fae8-916a-4a0a-89e9-924c191a1a0a
-- title:
--   GGConv Scalar W: is Uni iff
-- statement:
--   The GGConv Scalar W construction uses the is Uni iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L19-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L19-L19

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

theorem PI.GGConvScalarW.isUni_iff (x : GL (Fin k) F) : IsUni k x ↔ IsUTm (x : Matrix (Fin k) (Fin k) F) := by sorry
