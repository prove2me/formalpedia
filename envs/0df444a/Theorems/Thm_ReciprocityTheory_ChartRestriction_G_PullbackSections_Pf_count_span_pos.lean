-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_count_span_pos
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.count_span_pos
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T10:32:59.395202+00:00
-- url     : https://prove2.me/theorems/b505821f-a149-4e39-8c17-b62c97f3a825
-- title:
--   Pf: count span pos
-- statement:
--   The Pf construction uses the count span pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/PadicValNatAbsNormEqZero.lean#L261-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/PadicValNatAbsNormEqZero.lean#L261-L267

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.count_span_pos (E : Type) [Field E] [NumberField E] (ℓ : ℕ) (hℓ : ℓ.Prime) {P : Ideal (𝓞 E)}
    (hP : P.IsPrime) (hl : (ℓ : 𝓞 E) ∈ P) : 0 < (normalizedFactors (Ideal.span {(ℓ : 𝓞 E)})).count P := by sorry
