-- Prove2me | Theorems.Thm_PI_MSC_monomial_mem_sup
-- name    : PI.MSC.monomial_mem_sup
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:13.741107+00:00
-- url     : https://prove2.me/theorems/7b5544ce-48ad-4abd-a51a-8d90e1a398a1
-- title:
--   MSC: monomial mem sup
-- statement:
--   The MSC construction uses the monomial mem sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/ExistsCoeffNeZeroOfMemSpan.lean#L42-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/ExistsCoeffNeZeroOfMemSpan.lean#L42-L81

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSpanComplement_ExistsCoeffNeZeroOfMemSpan
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
open PI PI.MSC
open scoped MonomialOrder
variable {σ R : Type*} [CommRing R]

theorem PI.MSC.monomial_mem_sup (O : MonomialOrder σ) {ι : Type*} (c : ι → MvPolynomial σ R)
    (hlc : ∀ i, O.leadingCoeff (c i) = 1) (e : σ →₀ ℕ) (a : R) :
    monomial e a ∈ Submodule.span R (Set.range c) ⊔
      restrictSupport R (Set.range fun i => O.degree (c i))ᶜ := by sorry
