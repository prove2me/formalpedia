-- Prove2me | Theorems.Thm_PI_VolStabSW_fd_of_subset
-- name    : PI.VolStabSW.fd_of_subset
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T13:49:23.455167+00:00
-- url     : https://prove2.me/theorems/7b7be733-7539-4606-8851-fc54dc215316
-- title:
--   Vol Stab SW: fd of subset
-- statement:
--   The Vol Stab SW construction uses the fd of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/UnfoldAbs.lean#L27-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/UnfoldAbs.lean#L27-L41

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

theorem PI.VolStabSW.fd_of_subset {Γ : Subgroup G} [Countable Γ] {μ : Measure G} [μ.IsMulLeftInvariant]
    {s t : Set G} (h : IsFundamentalDomain Γ s μ) (hts : t ⊆ s) (ht : MeasurableSet t)
    (hnull : μ (s \ t) = 0) : IsFundamentalDomain Γ t μ := by sorry
