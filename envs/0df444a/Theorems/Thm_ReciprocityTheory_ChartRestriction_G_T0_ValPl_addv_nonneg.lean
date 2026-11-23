-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_addv_nonneg
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValPl.addv_nonneg
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:28:20.189669+00:00
-- url     : https://prove2.me/theorems/17781b1b-1cb3-4949-8ae6-94740a7ccc2d
-- title:
--   Val Pl: addv nonneg
-- statement:
--   The Val Pl construction uses the addv nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraMapOLInjective.lean#L69-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraMapOLInjective.lean#L69-L83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValPl
open IsDedekindDomain WithZero IsLocalRing
variable {S L : Type*} [CommRing S] [IsDedekindDomain S] [Field L] [Algebra S L]
  [IsFractionRing S L] (v : HeightOneSpectrum S)

theorem ReciprocityTheory.ChartRestriction.G.T0.ValPl.addv_nonneg (s : S) : 0 ≤ addv L v (algebraMap S L s) := by sorry
