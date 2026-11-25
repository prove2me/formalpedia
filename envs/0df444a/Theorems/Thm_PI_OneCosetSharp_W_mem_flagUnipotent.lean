-- Prove2me | Theorems.Thm_PI_OneCosetSharp_W_mem_flagUnipotent
-- name    : PI.OneCosetSharp.W.mem_flagUnipotent
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:35.495403+00:00
-- url     : https://prove2.me/theorems/90f2c3e8-abed-4490-bdf2-b4711c5eb2c7
-- title:
--   W: mem flag Unipotent
-- statement:
--   The W construction uses the mem flag Unipotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/MemFlagUnipotent.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/MemFlagUnipotent.lean#L40-L41

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_MemFlagUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W
open Loc LocE
variable {k : Type} [Field k] {n c : ℕ}

theorem PI.OneCosetSharp.W.mem_flagUnipotent {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) : r ∈ R1 k n c := by sorry
