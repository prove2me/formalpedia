-- Prove2me | Theorems.Thm_PI_VolStabSW_sum_rep_eq
-- name    : PI.VolStabSW.sum_rep_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:48:45.80652+00:00
-- url     : https://prove2.me/theorems/8e094fe1-515f-4272-9d14-678206afff50
-- title:
--   Vol Stab SW: sum rep eq
-- statement:
--   The Vol Stab SW construction uses the sum rep eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/UnfoldAbs.lean#L128-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/UnfoldAbs.lean#L128-L156

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
variable [MulAction G Y]

theorem PI.VolStabSW.sum_rep_eq {Γ H : Subgroup G} (y0 : Y) (hH : ∀ k : G, k ∈ H ↔ k • y0 = y0)
    (u : G → ℝ≥0∞) :
    ∑' x : orbS Γ y0, ∑' δ : (Γ ⊓ H).subgroupOf H, u (repO Γ y0 x * ((δ : H) : G)) =
      ∑' γ : Γ, u γ := by sorry
