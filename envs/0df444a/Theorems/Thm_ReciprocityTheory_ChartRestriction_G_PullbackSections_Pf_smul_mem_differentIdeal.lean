-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_smul_mem_differentIdeal
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.smul_mem_differentIdeal
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:33:30.438143+00:00
-- url     : https://prove2.me/theorems/b12cae23-0105-4f27-ad7f-8fb1f536d338
-- title:
--   Pf: smul mem different Ideal
-- statement:
--   The Pf construction uses the smul mem different Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/PadicValNatAbsNormEqZero.lean#L39-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/PadicValNatAbsNormEqZero.lean#L39-L47

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.smul_mem_differentIdeal (σ : E ≃ₐ[ℚ] E) {x : 𝓞 E} (hx : x ∈ differentIdeal ℤ (𝓞 E)) :
    σ • x ∈ differentIdeal ℤ (𝓞 E) := by sorry
