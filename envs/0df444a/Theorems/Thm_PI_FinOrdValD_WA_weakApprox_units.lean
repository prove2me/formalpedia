-- Prove2me | Theorems.Thm_PI_FinOrdValD_WA_weakApprox_units
-- name    : PI.FinOrdValD.WA.weakApprox_units
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T05:31:04.966335+00:00
-- url     : https://prove2.me/theorems/a6823b2e-244c-458d-918f-0cf9e0d73630
-- title:
--   WA: weak Approx units
-- statement:
--   The WA construction uses the weak Approx units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderValuation/WeakApprox.lean#L174-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderValuation/WeakApprox.lean#L174-L197

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderValuation_WeakApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero
open PI PI.FinOrdValD PI.FinOrdValD.WA
variable {L : Type*} [Field L] [NumberField L]

theorem PI.FinOrdValD.WA.weakApprox_units (T : Finset (HeightOneSpectrum (𝓞 L)))
    (x : (v : HeightOneSpectrum (𝓞 L)) → (v.adicCompletion L)ˣ) (e : HeightOneSpectrum (𝓞 L) → ℤ) :
    ∃ a : Lˣ, (∀ v ∈ T, Valued.v (algebraMap L (v.adicCompletion L) (a : L) * ((x v)⁻¹ : (v.adicCompletion L)ˣ) - 1) <
        exp (-e v)) ∧ ∀ σ : L →+* ℝ, 0 < σ (a : L) := by sorry
