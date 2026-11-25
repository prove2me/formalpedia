-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_exists_bound_primeIdealZetaSum_not_prime
-- name    : ReciprocityTheory.Neutral.Bridge.exists_bound_primeIdealZetaSum_not_prime
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:39:26.402991+00:00
-- url     : https://prove2.me/theorems/5ca50da3-0b8a-4557-a2bc-ab861b4d7aee
-- title:
--   Bridge: exists bound prime Ideal Zeta Sum not prime
-- statement:
--   The Bridge construction uses the exists bound prime Ideal Zeta Sum not prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean#L168-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean#L168-L175

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

theorem ReciprocityTheory.Neutral.Bridge.exists_bound_primeIdealZetaSum_not_prime :
    ∃ C : ℝ, ∀ s : ℝ, 1 < s →
      NumberField.Set.primeIdealZetaSum {𝔭 : HeightOneSpectrum (𝓞 K) | ¬ (Ideal.absNorm 𝔭.asIdeal).Prime} s ≤ C := by sorry
