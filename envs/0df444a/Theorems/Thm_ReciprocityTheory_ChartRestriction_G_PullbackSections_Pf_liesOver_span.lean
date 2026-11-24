-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_liesOver_span
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.liesOver_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:54.036586+00:00
-- url     : https://prove2.me/theorems/4f32c029-1939-4a0b-a5ce-4b371dfa0ec0
-- title:
--   Pf: lies Over span
-- statement:
--   The Pf construction uses the lies Over span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/PadicValNatAbsNormEqZero.lean#L191-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/PadicValNatAbsNormEqZero.lean#L191-L202

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.liesOver_span (E : Type) [Field E] [NumberField E] (ℓ : ℕ) (hℓ : ℓ.Prime) {P : Ideal (𝓞 E)}
    (hP : P.IsPrime) (hl : (ℓ : 𝓞 E) ∈ P) : P.LiesOver (Ideal.span {(ℓ : ℤ)}) := by sorry
