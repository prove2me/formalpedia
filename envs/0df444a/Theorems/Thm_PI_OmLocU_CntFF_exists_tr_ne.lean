-- Prove2me | Theorems.Thm_PI_OmLocU_CntFF_exists_tr_ne
-- name    : PI.OmLocU.CntFF.exists_tr_ne
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T08:16:20.097798+00:00
-- url     : https://prove2.me/theorems/a6b937af-8075-46a8-b791-5b758d2adbef
-- title:
--   Cnt FF: exists tr ne
-- statement:
--   The Cnt FF construction uses the exists tr ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnitaryOrbits/FFInert2Holds.lean#L253-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalUnitaryOrbits/FFInert2Holds.lean#L253-L265

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
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {σ : K →+* K}

theorem PI.OmLocU.CntFF.exists_tr_ne {k K : Type} [Field k] [Field K] [Algebra k K] (σ : K ≃ₐ[k] K)
    (hne : σ ≠ AlgEquiv.refl) : ∃ z : K, z + (σ : K →+* K) z ≠ 0 := by sorry
