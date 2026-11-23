-- Prove2me | Theorems.Thm_PI_GGConvScalarW_IsUTm_inv_val
-- name    : PI.GGConvScalarW.IsUTm.inv_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:26:45.595709+00:00
-- url     : https://prove2.me/theorems/054887ec-9312-4b48-9560-cd81e2e3b881
-- title:
--   Is UTm: inv val
-- statement:
--   The Is UTm construction uses the inv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L63-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ScalarConvolutionTrace/SuperdiagSgnConj.lean#L63-L81

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

theorem PI.GGConvScalarW.IsUTm.inv_val (u : GL (Fin k) F) (h : IsUTm (u : Matrix (Fin k) (Fin k) F)) :
    IsUTm ((u⁻¹ : GL (Fin k) F) : Matrix (Fin k) (Fin k) F) := by sorry
