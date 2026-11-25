-- Prove2me | Theorems.Thm_PI_VolStabS_sum_rep_eq
-- name    : PI.VolStabS.sum_rep_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:36:36.158268+00:00
-- url     : https://prove2.me/theorems/919d385f-8970-4a18-9021-be301b39fbb4
-- title:
--   Vol Stab S: sum rep eq
-- statement:
--   The Vol Stab S construction uses the sum rep eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/UnfoldAbs.lean#L61-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/UnfoldAbs.lean#L61-L96

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_UnfoldAbs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open MeasureTheory Set
open scoped ENNReal Pointwise
variable {G Y : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
variable [MulAction G Y]

theorem PI.VolStabS.sum_rep_eq {Γ H : Subgroup G} (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0)
    (u : G → ℝ≥0∞) :
    ∑' x : orbS Γ y0, ∑' δ : (Γ ⊓ H).subgroupOf H, u (repO Γ y0 x * ((δ : H) : G)) =
      ∑' γ : Γ, u γ := by sorry
