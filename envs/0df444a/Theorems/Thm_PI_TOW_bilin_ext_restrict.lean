-- Prove2me | Theorems.Thm_PI_TOW_bilin_ext_restrict
-- name    : PI.TOW.bilin_ext_restrict
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T05:37:30.859508+00:00
-- url     : https://prove2.me/theorems/24602cb5-e178-49ea-9b10-cbfe8496c568
-- title:
--   TOW: bilin ext restrict
-- statement:
--   The TOW construction uses the bilin ext restrict property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FockLin.lean#L130-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TensorOperator/FockLin.lean#L130-L143

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FockLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.TOW
open PI.TO

theorem PI.TOW.bilin_ext_restrict {K : Type} [CommRing K] {σ : Type*} (T : Set (σ →₀ ℕ))
    (Φ Ψ : MvPolynomial σ K →ₗ[K] MvPolynomial σ K →ₗ[K] K)
    (h : ∀ μ ∈ T, ∀ ν ∈ T, Φ (monomial μ 1) (monomial ν 1) = Ψ (monomial μ 1) (monomial ν 1)) :
    ∀ G ∈ restrictSupport K T, ∀ H ∈ restrictSupport K T, Φ G H = Ψ G H := by sorry
