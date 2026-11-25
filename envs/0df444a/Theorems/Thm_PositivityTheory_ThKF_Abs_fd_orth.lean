-- Prove2me | Theorems.Thm_PositivityTheory_ThKF_Abs_fd_orth
-- name    : PositivityTheory.ThKF.Abs.fd_orth
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:50:49.780373+00:00
-- url     : https://prove2.me/theorems/477a2253-51be-4c18-b06e-d239330098d5
-- title:
--   Abs: fd orth
-- statement:
--   The Abs construction uses the fd orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/SpanOrbitStab.lean#L51-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/SpanOrbitStab.lean#L51-L59

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_SpanOrbitStab
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKF PositivityTheory.ThKF.Abs
open scoped InnerProductSpace
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

theorem PositivityTheory.ThKF.Abs.fd_orth {K : Type} [Group K] (κ : K →* Module.End ℂ U) (W : Submodule ℂ U) [FiniteDimensional ℂ W]
    [FiniteDimensional ℂ (homs κ W)] : FiniteDimensional ℂ ↥(ck (homs κ W))ᗮ := by sorry
