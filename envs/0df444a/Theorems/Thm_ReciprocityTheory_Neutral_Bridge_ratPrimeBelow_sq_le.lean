-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_ratPrimeBelow_sq_le
-- name    : ReciprocityTheory.Neutral.Bridge.ratPrimeBelow_sq_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:04:56.899724+00:00
-- url     : https://prove2.me/theorems/e725dec0-da82-5495-9246-cd91b6cfd26f
-- title:
--   Bridge: rat Prime Below sq le
-- statement:
--   The Bridge construction uses the rat Prime Below sq le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean#L66-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean#L66-L76

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

theorem ReciprocityTheory.Neutral.Bridge.ratPrimeBelow_sq_le (𝔭 : HeightOneSpectrum (𝓞 K)) (h : ¬ (Ideal.absNorm 𝔭.asIdeal).Prime) :
    ratPrimeBelow 𝔭 ^ 2 ≤ Ideal.absNorm 𝔭.asIdeal := by sorry
