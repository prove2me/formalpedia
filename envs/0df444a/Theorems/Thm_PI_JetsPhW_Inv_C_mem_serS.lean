-- Prove2me | Theorems.Thm_PI_JetsPhW_Inv_C_mem_serS
-- name    : PI.JetsPhW.Inv.C_mem_serS
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:12:46.779546+00:00
-- url     : https://prove2.me/theorems/0dfcf9ae-91c3-5baa-8dde-41d8c44a3e1a
-- title:
--   Inv: C mem ser S
-- statement:
--   The Inv construction uses the C mem ser S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/InvOmega.lean#L110-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/InvOmega.lean#L110-L117

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_JetsPhW
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InverseOmegaHolds
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerTer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_InvOmega
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical
open PI PI.JetsPhW PI.JetsPhW.Inv
variable {p : ℕ} [Fact p.Prime]

theorem PI.JetsPhW.Inv.C_mem_serS {S : Subring ℂ_[p]} {a : ℂ_[p]} (ha : a ∈ S) :
    algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a ∈ serS S := by sorry
