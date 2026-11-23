-- Prove2me | Theorems.Thm_PI_GGConvScalarW_psiU_ne_zero
-- name    : PI.GGConvScalarW.psiU_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:20.733034+00:00
-- url     : https://prove2.me/theorems/ff2e982b-634f-4941-b09b-399a87426e9a
-- title:
--   GGConv Scalar W: psi U ne zero
-- statement:
--   The GGConv Scalar W construction uses the psi U ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L111-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L111-L116

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

theorem PI.GGConvScalarW.psiU_ne_zero (ψ₀ : AddChar F ℂ) (x : GL (Fin k) F) : psiU ψ₀ x ≠ 0 := by sorry
