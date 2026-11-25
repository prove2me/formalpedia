-- Prove2me | Theorems.Thm_PI_UnitaryGroupMassFormula_FlagGramNonneg_Jpq_mulVec_of
-- name    : PI.UnitaryGroupMassFormula.FlagGramNonneg.Jpq_mulVec_of
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T05:38:41.739808+00:00
-- url     : https://prove2.me/theorems/859f005c-45c0-480b-9304-a53990ce60d3
-- title:
--   Flag Gram Nonneg: Jpq mul Vec of
-- statement:
--   The Flag Gram Nonneg construction uses the Jpq mul Vec of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/HasSignatureExistsNonneg.lean#L32-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FlagGramNonnegativity/HasSignatureExistsNonneg.lean#L32-L37

import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_HasSignatureExistsNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PI.FlagGramNonneg
open scoped ComplexOrder
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.FlagGramNonneg

theorem PI.UnitaryGroupMassFormula.FlagGramNonneg.Jpq_mulVec_of {p q : ℕ} (u : Fin p ⊕ Fin q → ℂ) (hu : ∀ j, u (Sum.inr j) = 0) :
    Jpq p q *ᵥ u = u := by sorry
