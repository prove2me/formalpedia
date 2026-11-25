-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_mem_primesOverFinset_ratPrimeBelow
-- name    : ReciprocityTheory.Neutral.Bridge.mem_primesOverFinset_ratPrimeBelow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:05:28.365361+00:00
-- url     : https://prove2.me/theorems/9e2e1860-4969-467e-80b2-e0a7294c9ed4
-- title:
--   Bridge: mem primes Over Finset rat Prime Below
-- statement:
--   The Bridge construction uses the mem primes Over Finset rat Prime Below property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean#L78-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean#L78-L85

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

theorem ReciprocityTheory.Neutral.Bridge.mem_primesOverFinset_ratPrimeBelow (𝔭 : HeightOneSpectrum (𝓞 K)) :
    𝔭.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {((ratPrimeBelow 𝔭 : ℕ) : ℤ)}) (𝓞 K) := by sorry
