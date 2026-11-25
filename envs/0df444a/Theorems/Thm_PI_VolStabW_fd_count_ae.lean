-- Prove2me | Theorems.Thm_PI_VolStabW_fd_count_ae
-- name    : PI.VolStabW.fd_count_ae
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T08:41:17.74294+00:00
-- url     : https://prove2.me/theorems/30c24d04-16fe-5ca5-8822-7397c21381a9
-- title:
--   Vol Stab W: fd count ae
-- statement:
--   The Vol Stab W construction uses the fd count ae property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/UnfoldAbs.lean#L43-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/UnfoldAbs.lean#L43-L62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnfoldAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]

theorem PI.VolStabW.fd_count_ae {Γ : Subgroup G} [Countable Γ] {μ : Measure G} {s : Set G}
    (h : IsFundamentalDomain Γ s μ) :
    ∀ᵐ g ∂μ, ∑' γ : Γ, s.indicator (fun _ => (1 : ℝ≥0∞)) ((γ : G) * g) = 1 := by sorry
