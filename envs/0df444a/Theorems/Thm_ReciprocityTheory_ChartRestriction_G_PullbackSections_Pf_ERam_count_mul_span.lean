-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_count_mul_span
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.count_mul_span
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T10:32:36.409021+00:00
-- url     : https://prove2.me/theorems/228815d6-a318-4f46-a448-bc1f3b765031
-- title:
--   ERam: count mul span
-- statement:
--   The ERam construction uses the count mul span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamVal.lean#L165-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamVal.lean#L165-L173

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_PadicValNatAbsNormEqZero
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamVal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open NumberField UniqueFactorizationMonoid Formalism.L2.Pj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {E : Type} [Field E] [NumberField E]
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {k : Type} [Field k] [Algebra V k]
  [IsFractionRing V k]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.count_mul_span {P : Ideal (𝓞 E)} {x y : 𝓞 E} (hx : x ≠ 0) (hy : y ≠ 0) :
    (normalizedFactors (Ideal.span {x * y})).count P =
      (normalizedFactors (Ideal.span {x})).count P + (normalizedFactors (Ideal.span {y})).count P := by sorry
