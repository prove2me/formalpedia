-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_count_smul
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.count_smul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:32:56.487082+00:00
-- url     : https://prove2.me/theorems/68931d5b-1751-5bb0-a776-61e6a9d8780a
-- title:
--   Pf: count smul
-- statement:
--   The Pf construction uses the count smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/PadicValNatAbsNormEqZero.lean#L62-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/PadicValNatAbsNormEqZero.lean#L62-L78

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_DiffAtOddSt
import Definitions.Def_Lemmata_MiscLemmasK_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaL_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Pointwise
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.count_smul (σ : E ≃ₐ[ℚ] E) {P X : Ideal (𝓞 E)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hQ : (σ • P).IsPrime)
    (hQ0 : σ • P ≠ ⊥) (hX : X ≠ ⊥) :
    (normalizedFactors (σ • X)).count (σ • P) = (normalizedFactors X).count P := by sorry
