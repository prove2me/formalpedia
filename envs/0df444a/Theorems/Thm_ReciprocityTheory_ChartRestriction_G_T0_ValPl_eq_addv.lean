-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValPl_eq_addv
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValPl.eq_addv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T01:11:23.694189+00:00
-- url     : https://prove2.me/theorems/1072e1b7-b75f-4638-8575-e10b0938dd3b
-- title:
--   Val Pl: eq addv
-- statement:
--   The Val Pl construction uses the eq addv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraMapOLInjective.lean#L103-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/AlgebraMapOLInjective.lean#L103-L175

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

theorem ReciprocityTheory.ChartRestriction.G.T0.ValPl.eq_addv (w : AddValuation L (WithTop ℤ)) (hw : IsNormDiscrete w)
    (h0 : ∀ s : S, 0 ≤ w (algebraMap S L s))
    (hQ : ∀ s : S, 0 < w (algebraMap S L s) ↔ s ∈ v.asIdeal) : w = addv L v := by sorry
