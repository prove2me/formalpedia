-- Prove2me | Theorems.Thm_PI_JetsPhW_Inv_X_mem_serS
-- name    : PI.JetsPhW.Inv.X_mem_serS
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:13:12.25867+00:00
-- url     : https://prove2.me/theorems/6ceeac71-020a-4f5c-85a9-bba6959815d3
-- title:
--   Inv: X mem ser S
-- statement:
--   The Inv construction uses the X mem ser S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/InvOmega.lean#L103-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/JetIntegrality/InvOmega.lean#L103-L108

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

theorem PI.JetsPhW.Inv.X_mem_serS (S : Subring ℂ_[p]) : (PowerSeries.X : PowerSeries ℂ_[p]) ∈ serS S := by sorry
