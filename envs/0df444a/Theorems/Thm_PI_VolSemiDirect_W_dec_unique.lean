-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_dec_unique
-- name    : PI.VolSemiDirect.W.dec_unique
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:36:34.216987+00:00
-- url     : https://prove2.me/theorems/8d2ca7bc-a75b-5548-a850-d10c7c8e4d71
-- title:
--   W: dec unique
-- statement:
--   The W construction uses the dec unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/VolumeQuotientHolds.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/VolumeQuotientHolds.lean#L20-L25

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_ClosedStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_FundamentalDomainExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SemidirectVolume_VolumeQuotientHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolSemiDirect PI.VolSemiDirect.W
open MeasureTheory
variable {X : Type} [Group X] [TopologicalSpace X] {K N H : Subgroup X}

theorem PI.VolSemiDirect.W.dec_unique (e : (N × H) ≃ₜ K) (he : ∀ p : N × H, ((e p : K) : X) = (p.1 : X) * (p.2 : X))
    {n1 n2 : N} {h1 h2 : H} (h : (n1 : X) * (h1 : X) = (n2 : X) * (h2 : X)) :
    n1 = n2 ∧ h1 = h2 := by sorry
