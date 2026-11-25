-- Prove2me | Theorems.Thm_PI_MSC_isCompl_map_rename
-- name    : PI.MSC.isCompl_map_rename
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:35:19.484881+00:00
-- url     : https://prove2.me/theorems/5cab6a59-6bc5-45cf-8477-fb5dfa02bc60
-- title:
--   MSC: is Compl map rename
-- statement:
--   The MSC construction uses the is Compl map rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/ExistsCoeffNeZeroOfMemSpan.lean#L83-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/MinorSpanComplement/ExistsCoeffNeZeroOfMemSpan.lean#L83-L123

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

theorem PI.MSC.isCompl_map_rename (O : MonomialOrder σ) {τ : Type*} {φ : σ → τ}
    (hφ : Function.Injective φ) {ι : Type*} (c : ι → MvPolynomial σ R)
    (hinj : Function.Injective fun i => O.degree (c i)) (hlc : ∀ i, O.leadingCoeff (c i) = 1) :
    IsCompl (Submodule.map (rename φ).toLinearMap (Submodule.span R (Set.range c)))
      (restrictSupport R (Finsupp.mapDomain φ '' Set.range fun i => O.degree (c i))ᶜ) := by sorry
