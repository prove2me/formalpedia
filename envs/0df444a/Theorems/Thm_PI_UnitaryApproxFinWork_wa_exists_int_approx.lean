-- Prove2me | Theorems.Thm_PI_UnitaryApproxFinWork_wa_exists_int_approx
-- name    : PI.UnitaryApproxFinWork.wa_exists_int_approx
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:32:09.423319+00:00
-- url     : https://prove2.me/theorems/eded9d08-2d2c-4178-a427-4f7785ce0ed2
-- title:
--   Unitary Approx Fin Work: wa exists int approx
-- statement:
--   The Unitary Approx Fin Work construction uses the wa exists int approx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/WeakApproximationFiniteUnitary.lean#L53-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryApproximation/WeakApproximationFiniteUnitary.lean#L53-L101

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproximationFiniteUnitary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open PI PI.UnitaryApproxFinWork
variable {F : Type} [Field F] [NumberField F]

theorem PI.UnitaryApproxFinWork.wa_exists_int_approx (T : Finset (HeightOneSpectrum (𝓞 F)))
    (b : HeightOneSpectrum (𝓞 F) → F) :
    ∃ a : F, ∀ v ∈ T, v.valuation F (a - b v) ≤ 1 := by sorry
