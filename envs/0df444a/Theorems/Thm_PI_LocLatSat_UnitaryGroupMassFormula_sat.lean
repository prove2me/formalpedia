-- Prove2me | Theorems.Thm_PI_LocLatSat_UnitaryGroupMassFormula_sat
-- name    : PI.LocLatSat.UnitaryGroupMassFormula.sat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:24.991344+00:00
-- url     : https://prove2.me/theorems/91c56c3a-ebe4-421b-9bee-0adcb796717a
-- title:
--   Unitary Group Mass Formula: sat
-- statement:
--   The Unitary Group Mass Formula construction uses the sat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeSaturation/LocLatSat.lean#L36-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeSaturation/LocLatSat.lean#L36-L85

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_BcGSmulR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_LocLatSat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped nonZeroDivisors
open PI PI.LocLatSat PI.LocLatSat.UnitaryGroupMassFormula
variable {R K S : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [CommRing S] (φ : K →+* S) (O : Subring S) {n : ℕ}

theorem PI.LocLatSat.UnitaryGroupMassFormula.sat (Λ : Submodule R (Fin n → K)) (hΛ : Λ.FG) (W : Submodule K (Fin n → K)) :
    (latG φ O (Λ ⊓ W.restrictScalars R) : Set (Fin n → S)) =
      (latG φ O Λ : Set (Fin n → S)) ∩ Submodule.span S (bcG φ '' (W : Set (Fin n → K))) := by sorry
