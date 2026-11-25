-- Prove2me | Theorems.Thm_PI_OneCosetSharp_W_R1cond_symm
-- name    : PI.OneCosetSharp.W.R1cond_symm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:16:28.085746+00:00
-- url     : https://prove2.me/theorems/0816f891-ee86-46af-961b-1bcf9b84eb88
-- title:
--   W: R1cond symm
-- statement:
--   The W construction uses the R1cond symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/MemFlagUnipotent.lean#L27-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/MemFlagUnipotent.lean#L27-L38

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

theorem PI.OneCosetSharp.W.R1cond_symm {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : R1cond k n c r) : R1cond k n c r.symm := by sorry
