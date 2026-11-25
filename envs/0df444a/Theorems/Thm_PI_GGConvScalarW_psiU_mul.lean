-- Prove2me | Theorems.Thm_PI_GGConvScalarW_psiU_mul
-- name    : PI.GGConvScalarW.psiU_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:11.696047+00:00
-- url     : https://prove2.me/theorems/998ae879-1bef-4b23-a2fb-f3c50d9bd1fc
-- title:
--   GGConv Scalar W: psi U mul
-- statement:
--   The GGConv Scalar W construction uses the psi U mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L89-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L89-L92

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

theorem PI.GGConvScalarW.psiU_mul (ψ₀ : AddChar F ℂ) {x y : GL (Fin k) F} (hx : IsUni k x) (hy : IsUni k y) :
    psiU ψ₀ (x * y) = psiU ψ₀ x * psiU ψ₀ y := by sorry
