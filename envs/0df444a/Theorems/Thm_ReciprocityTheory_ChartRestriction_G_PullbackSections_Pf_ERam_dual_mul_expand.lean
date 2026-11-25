-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_Pf_ERam_dual_mul_expand
-- name    : ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.dual_mul_expand
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:33:43.376853+00:00
-- url     : https://prove2.me/theorems/914c0ada-e1b9-5766-9f68-cb9a9c3e0b90
-- title:
--   ERam: dual mul expand
-- statement:
--   The ERam construction uses the dual mul expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamData.lean#L49-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PullbackSections/HolomorphicFamilies/EigRamData.lean#L49-L66

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamCore
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_IdemDataBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_EigRamData
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
open NumberField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam
variable {E : Type} [Field E] [NumberField E]

theorem ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.ERam.dual_mul_expand (a : 𝓞 E) (i : Module.Free.ChooseBasisIndex ℤ (𝓞 E)) :
    (a : E) * TB.trDual (integralBasis E) i =
      ∑ j, (((RingOfIntegers.basis E).repr (a * RingOfIntegers.basis E j) i : ℤ) : ℚ) • TB.trDual (integralBasis E) j := by sorry
