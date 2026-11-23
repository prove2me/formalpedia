-- Prove2me | Theorems.Thm_PI_OmLocU_CntFF_exists_aniso2
-- name    : PI.OmLocU.CntFF.exists_aniso2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:37.658158+00:00
-- url     : https://prove2.me/theorems/caa8cfc3-071a-4a5b-8d2f-fa0568f517eb
-- title:
--   Cnt FF: exists aniso2
-- statement:
--   The Cnt FF construction uses the exists aniso2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnitaryOrbits/FFInert2Holds.lean#L15-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnitaryOrbits/FFInert2Holds.lean#L15-L33

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensFFS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_FFInert2Holds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmLocU PI.OmLocU.CntFF
open Module PI.VolStabSW PI.VolStabSW.FFHS
variable {K : Type} [Field K] {σ : K →+* K} {V : Type} [AddCommGroup V] [Module K V] {h : V → V → K}

theorem PI.OmLocU.CntFF.exists_aniso2 (h2 : ∃ z : K, z + σ z ≠ 0) (hs : IsHS σ h) (x : V) (hx : x ≠ 0) :
    ∃ e, h e e ≠ 0 := by sorry
