-- Prove2me | Theorems.Thm_PI_OneCosetSharp_W_P2_nums_le
-- name    : PI.OneCosetSharp.W.P2.nums_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:35:08.412731+00:00
-- url     : https://prove2.me/theorems/40e2e06b-92c9-46dd-b1e6-c8a8b3fc803c
-- title:
--   P2: nums le
-- statement:
--   The P2 construction uses the nums le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/AllowColLt.lean#L166-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/AllowColLt.lean#L166-L169

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_KappaZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_projection2_AllowColLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI.OneCosetSharp PI.OneCosetSharp.Loc PI.OneCosetSharp.LocE
noncomputable section
open PI PI.OneCosetSharp PI.OneCosetSharp.W PI.OneCosetSharp.W.P2
variable {k : Type} [Field k]
variable {k₀ m t b : ℕ}

theorem PI.OneCosetSharp.W.P2.nums_le {k₀ m t j n' c n : ℕ} (h : Nums k₀ m t j n' c n) : k₀ ≤ n ∧ k₀ + m - 1 ≤ n + c := by sorry
