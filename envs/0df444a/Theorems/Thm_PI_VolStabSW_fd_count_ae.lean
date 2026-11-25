-- Prove2me | Theorems.Thm_PI_VolStabSW_fd_count_ae
-- name    : PI.VolStabSW.fd_count_ae
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T13:49:27.364135+00:00
-- url     : https://prove2.me/theorems/9f3384c6-1af0-4ffa-a54b-be11ccf2a0a2
-- title:
--   Vol Stab SW: fd count ae
-- statement:
--   The Vol Stab SW construction uses the fd count ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/UnfoldAbs.lean#L43-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/UnfoldAbs.lean#L43-L71

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_UnfoldAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]

theorem PI.VolStabSW.fd_count_ae {Γ : Subgroup G} [Countable Γ] {μ : Measure G} {s : Set G}
    (h : IsFundamentalDomain Γ s μ) :
    ∀ᵐ g ∂μ, ∑' γ : Γ, s.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * g) = 1 := by sorry
