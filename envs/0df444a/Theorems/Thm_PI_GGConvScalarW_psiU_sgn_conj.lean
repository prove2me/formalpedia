-- Prove2me | Theorems.Thm_PI_GGConvScalarW_psiU_sgn_conj
-- name    : PI.GGConvScalarW.psiU_sgn_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:27:09.597937+00:00
-- url     : https://prove2.me/theorems/5bdb1221-cd61-4ae8-9e7b-a439e8fdac45
-- title:
--   GGConv Scalar W: psi U sgn conj
-- statement:
--   The GGConv Scalar W construction uses the psi U sgn conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L160-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L160-L164

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

theorem PI.GGConvScalarW.psiU_sgn_conj (ψ₀ : AddChar F ℂ) (u : GL (Fin k) F) :
    psiU ψ₀ (sgn k * u * sgn k) * psiU ψ₀ u = 1 := by sorry
