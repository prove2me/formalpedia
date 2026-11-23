-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_natCast_ne_zero_oe
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.natCast_ne_zero_oe
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:48:09.45045+00:00
-- url     : https://prove2.me/theorems/8ad2ea11-14d9-4e63-b6f6-7ab5a4d73779
-- title:
--   Pf: nat Cast ne zero oe
-- statement:
--   The Pf construction uses the nat Cast ne zero oe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/PadicValNatAbsNormEqZero.lean#L96-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/PadicValNatAbsNormEqZero.lean#L96-L100

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

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.natCast_ne_zero_oe (ℓ : ℕ) [hℓ : Fact ℓ.Prime] : (ℓ : 𝓞 E) ≠ 0 := by sorry
