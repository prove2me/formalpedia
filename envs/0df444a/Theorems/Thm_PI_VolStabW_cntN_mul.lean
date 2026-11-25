-- Prove2me | Theorems.Thm_PI_VolStabW_cntN_mul
-- name    : PI.VolStabW.cntN_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T05:42:53.165907+00:00
-- url     : https://prove2.me/theorems/d6e99339-a420-4a7b-9139-e3da7de2a323
-- title:
--   Vol Stab W: cnt N mul
-- statement:
--   The Vol Stab W construction uses the cnt N mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/UnfoldAbs.lean#L114-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/UnfoldAbs.lean#L114-L119

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
variable [MulAction G Y]

theorem PI.VolStabW.cntN_mul (Γ : Subgroup G) (A : Set G) {γ : G} (hγ : γ ∈ Γ) (g : G) :
    cntN Γ A (γ * g) = cntN Γ A g := by sorry
