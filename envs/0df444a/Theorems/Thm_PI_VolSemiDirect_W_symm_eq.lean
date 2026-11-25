-- Prove2me | Theorems.Thm_PI_VolSemiDirect_W_symm_eq
-- name    : PI.VolSemiDirect.W.symm_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:37:37.430685+00:00
-- url     : https://prove2.me/theorems/0fa0107e-262a-5e74-9e43-85f4377c7cd8
-- title:
--   W: symm eq
-- statement:
--   The W construction uses the symm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/VolumeQuotientHolds.lean#L27-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/SemidirectVolume/VolumeQuotientHolds.lean#L27-L30

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

theorem PI.VolSemiDirect.W.symm_eq (e : (N × H) ≃ₜ K) (he : ∀ p : N × H, ((e p : K) : X) = (p.1 : X) * (p.2 : X))
    {k : K} {n : N} {h : H} (hk : (k : X) = (n : X) * (h : X)) : e.symm k = (n, h) := by sorry
