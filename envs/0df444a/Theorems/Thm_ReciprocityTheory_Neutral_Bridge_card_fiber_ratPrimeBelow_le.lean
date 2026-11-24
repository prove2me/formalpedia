-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_card_fiber_ratPrimeBelow_le
-- name    : ReciprocityTheory.Neutral.Bridge.card_fiber_ratPrimeBelow_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:17.70906+00:00
-- url     : https://prove2.me/theorems/9c3cedd5-0dc9-42aa-be90-f43e6cade6e0
-- title:
--   Bridge: card fiber rat Prime Below le
-- statement:
--   The Bridge construction uses the card fiber rat Prime Below le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean#L109-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean#L109-L123

import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TendstoPrimeIdealZetaSumUniv
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_ExistsPrimeAbsNormOfHasDirichletDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open NumberField IsDedekindDomain Filter Topology
variable {K : Type*} [Field K] [NumberField K]

theorem ReciprocityTheory.Neutral.Bridge.card_fiber_ratPrimeBelow_le {ι : Type*} (g : ι → HeightOneSpectrum (𝓞 K)) (hg : Function.Injective g)
    (F : Finset ι) (p : ℕ) (hp : p.Prime) :
    (F.filter fun x => ratPrimeBelow (g x) = p).card ≤ Module.finrank ℚ K := by sorry
