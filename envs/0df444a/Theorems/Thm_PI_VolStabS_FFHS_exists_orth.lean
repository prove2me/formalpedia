-- Prove2me | Theorems.Thm_PI_VolStabS_FFHS_exists_orth
-- name    : PI.VolStabS.FFHS.exists_orth
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T08:36:56.402108+00:00
-- url     : https://prove2.me/theorems/6ca2bcd6-1991-4253-b587-dba530061078
-- title:
--   FFHS: exists orth
-- statement:
--   The FFHS construction uses the exists orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFHS.lean#L133-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerVolume/LocDensFFHS.lean#L133-L165

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_LocDensFFHS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.FFHS
open Module
variable {K : Type} [Field K] {σ : K →+* K}

theorem PI.VolStabS.FFHS.exists_orth (h2 : (2 : K) ≠ 0) : ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h : V → V → K), IsHS σ h → finrank K V = m →
    ∃ f : Fin m → V, (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, h (f i) (f i) ≠ 0 := by sorry
