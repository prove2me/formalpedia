-- Prove2me | Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_pos_perp
-- name    : PI.AutLzFinite.SlopeTestRemainingChoices.pos_perp
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T05:24:06.632221+00:00
-- url     : https://prove2.me/theorems/4979fb47-ea3a-4999-a379-862969b5feab
-- title:
--   Slope Test Remaining Choices: pos perp
-- statement:
--   The Slope Test Remaining Choices construction uses the pos perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MulVecMapInjective.lean#L69-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/MulVecMapInjective.lean#L69-L148

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_SylvesterLe
import Definitions.Def_Lemmata_GeneralBFactUpperAltForm_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_MulVecMapInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AutLzFinite PI.AutLzFinite.SlopeTestRemainingChoices
open Matrix Formalism.BasicNotions
variable {E : Type} [Field E] [NumberField E] [StarRing E] (S : HSpace E)

theorem PI.AutLzFinite.SlopeTestRemainingChoices.pos_perp (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    (τ : E →+* ℂ) {p q : ℕ} (hsig : Formalism.UG.HasSignature (S.gram.map τ) p q) {r : ℕ} (hq : q ≤ r + 1)
    (e : Fin r → S.V) (he : LinearIndependent E e) (hee : ∀ a b, S.hT (e a) (e b) = 0)
    (z : S.V) (hez : ∀ a, S.hT (e a) z = 0) (hzz : (τ (S.hT z z)).re < 0)
    (y : S.V) (hey : ∀ a, S.hT (e a) y = 0) (hzy : S.hT z y = 0)
    (hyX : y ∉ Submodule.span E (Set.range e)) : 0 < (τ (S.hT y y)).re := by sorry
