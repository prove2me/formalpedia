-- Prove2me | Theorems.Thm_PI_FinOrdValD_WA_weakApprox
-- name    : PI.FinOrdValD.WA.weakApprox
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:29:05.769175+00:00
-- url     : https://prove2.me/theorems/5e4ef27f-4049-4bb3-bf58-3e8e3d84ebbb
-- title:
--   WA: weak Approx
-- statement:
--   The WA construction uses the weak Approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderValuation/WeakApprox.lean#L89-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FiniteOrderValuation/WeakApprox.lean#L89-L172

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

theorem PI.FinOrdValD.WA.weakApprox (T : Finset (HeightOneSpectrum (𝓞 L)))
    (x : (v : HeightOneSpectrum (𝓞 L)) → v.adicCompletion L)
    (γ : HeightOneSpectrum (𝓞 L) → ℤᵐ⁰) (hγ : ∀ v ∈ T, γ v ≠ 0) :
    ∃ a : L, a ≠ 0 ∧ (∀ v ∈ T, Valued.v (algebraMap L (v.adicCompletion L) a - x v) < γ v) ∧
      ∀ σ : L →+* ℝ, 0 < σ a := by sorry
