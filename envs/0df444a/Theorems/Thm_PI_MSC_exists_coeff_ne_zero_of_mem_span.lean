-- Prove2me | Theorems.Thm_PI_MSC_exists_coeff_ne_zero_of_mem_span
-- name    : PI.MSC.exists_coeff_ne_zero_of_mem_span
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:34:53.041556+00:00
-- url     : https://prove2.me/theorems/3abeb136-a1e1-5c90-aa7f-59cea47c22e9
-- title:
--   MSC: exists coeff ne zero of mem span
-- statement:
--   The MSC construction uses the exists coeff ne zero of mem span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/ExistsCoeffNeZeroOfMemSpan.lean#L13-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/ExistsCoeffNeZeroOfMemSpan.lean#L13-L40

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

theorem PI.MSC.exists_coeff_ne_zero_of_mem_span (O : MonomialOrder σ) {ι : Type*}
    (c : ι → MvPolynomial σ R) (hinj : Function.Injective fun i => O.degree (c i))
    (hlc : ∀ i, O.leadingCoeff (c i) = 1) {g : MvPolynomial σ R}
    (hg : g ∈ Submodule.span R (Set.range c)) (hg0 : g ≠ 0) :
    ∃ i, g.coeff (O.degree (c i)) ≠ 0 := by sorry
