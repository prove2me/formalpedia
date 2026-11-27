-- Prove2me | Theorems.Thm_PI_VolStabSW_cntN_mul
-- name    : PI.VolStabSW.cntN_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:49:06.671254+00:00
-- url     : https://prove2.me/theorems/a62bc908-0297-40c5-8eca-b1b0a3cf9cec
-- title:
--   Vol Stab SW: cnt N mul
-- statement:
--   The Vol Stab SW construction uses the cnt N mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/UnfoldAbs.lean#L118-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/UnfoldAbs.lean#L118-L126

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

theorem PI.VolStabSW.cntN_mul (Γ : Subgroup G) (A : Set G) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    cntN Γ A (γ * g) = cntN Γ A g := by sorry
