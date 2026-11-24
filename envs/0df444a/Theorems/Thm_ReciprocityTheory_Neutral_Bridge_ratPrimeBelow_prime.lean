-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_ratPrimeBelow_prime
-- name    : ReciprocityTheory.Neutral.Bridge.ratPrimeBelow_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:47.17831+00:00
-- url     : https://prove2.me/theorems/fc215aad-c77d-4726-b6cb-1397c2ae076f
-- title:
--   Bridge: rat Prime Below prime
-- statement:
--   The Bridge construction uses the rat Prime Below prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean#L30-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean#L30-L39

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

theorem ReciprocityTheory.Neutral.Bridge.ratPrimeBelow_prime (𝔭 : HeightOneSpectrum (𝓞 K)) : (ratPrimeBelow 𝔭).Prime := by sorry
