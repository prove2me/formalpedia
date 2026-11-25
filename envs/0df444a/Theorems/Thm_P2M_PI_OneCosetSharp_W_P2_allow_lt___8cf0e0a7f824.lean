-- Prove2me | Theorems.Thm_P2M_PI_OneCosetSharp_W_P2_allow_lt___8cf0e0a7f824
-- name    : P2M_PI_OneCosetSharp_W_P2_allow_lt___8cf0e0a7f824
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T04:57:04.854705+00:00
-- url     : https://prove2.me/theorems/1f8e4d09-966b-495c-99af-d09eece98fb8
-- title:
--   P2 M PI One Coset Sharp W P2 allow lt   8cf0e0a7f824: P2 M PI One Coset Sharp W P2 allow lt   8cf0e0a7f824
-- statement:
--   The P2 M PI One Coset Sharp W P2 allow lt   8cf0e0a7f824 construction uses the P2 M PI One Coset Sharp W P2 allow lt   8cf0e0a7f824 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/AllowColLt.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/projection2/AllowColLt.lean#L31-L34

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

theorem P2M_PI_OneCosetSharp_W_P2_allow_lt___8cf0e0a7f824 {k₀ m t N p q : ℕ} (hq : q < k₀ + m - 1) (h : Allow k₀ m t N p q) : φ k₀ m p < φ k₀ m q := by sorry

alias «PI».«OneCosetSharp».«W».«P2».«allow_lt_φ» := P2M_PI_OneCosetSharp_W_P2_allow_lt___8cf0e0a7f824
