-- Prove2me | Theorems.Thm_PI_LocLatSat_UnitaryGroupMassFormula_step
-- name    : PI.LocLatSat.UnitaryGroupMassFormula.step
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T05:35:57.937141+00:00
-- url     : https://prove2.me/theorems/6c44c06e-4693-5a23-aaca-53beccf05893
-- title:
--   Unitary Group Mass Formula: step
-- statement:
--   The Unitary Group Mass Formula construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeSaturation/BcGSmulR.lean#L44-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LocalLatticeSaturation/BcGSmulR.lean#L44-L126

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LocLatSat
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalLatticeSaturation_BcGSmulR
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

theorem PI.LocLatSat.UnitaryGroupMassFormula.step (Λ : Submodule R (Fin n → K)) (f : (Fin n → K) →ₗ[K] K)
    (hI : IsFractional R⁰ (Λ.map (f.restrictScalars R)))
    {x : Fin n → S} (hx : x ∈ latG φ O Λ) (h0 : fP φ f x = 0) :
    x ∈ latG φ O (Λ ⊓ (LinearMap.ker f).restrictScalars R) := by sorry
