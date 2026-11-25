-- Prove2me | Theorems.Thm_PI_AutLzFinite_SlopeTestRemainingChoices_indSet_finite
-- name    : PI.AutLzFinite.SlopeTestRemainingChoices.indSet_finite
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T05:24:19.611645+00:00
-- url     : https://prove2.me/theorems/eddab791-9d34-472e-aa5b-d8bb37aa6c4d
-- title:
--   Slope Test Remaining Choices: ind Set finite
-- statement:
--   The Slope Test Remaining Choices construction uses the ind Set finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/IndSetFinite.lean#L19-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LatticeAutomorphismFiniteness/IndSetFinite.lean#L19-L151

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_FiniteOfIntegralBound
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismFiniteness_IndSetFinite
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
open Formalism.BasicNotions NumberField
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem PI.AutLzFinite.SlopeTestRemainingChoices.indSet_finite (hstar : ∀ (τ : E →+* ℂ) (a : E), τ (star a) = starRingEnd ℂ (τ a))
    (X P : Submodule E S.V) (hPX : ∀ x ∈ X, ∀ y ∈ P, S.hT x y = 0) (z : S.V) (hzP : z ∈ P)
    (hzz : ∀ τ : E →+* ℂ, (τ (S.hT z z)).re < 0)
    (hpos : ∀ τ : E →+* ℂ, ∀ y ∈ P, S.hT z y = 0 → y ∉ X → 0 < (τ (S.hT y y)).re)
    (Λ : Submodule (𝓞 E) S.V) (hΛ : Submodule.span E (Λ : Set S.V) = ⊤)
    (hint : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ (S.hT x y)) (hzΛ : z ∈ Λ) :
    (indSet X P z Λ).Finite := by sorry
