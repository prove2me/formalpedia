-- Prove2me | Theorems.Thm_ReciprocityTheory_Neutral_Bridge_exists_prime_absNorm_of_hasDirichletDensity
-- name    : ReciprocityTheory.Neutral.Bridge.exists_prime_absNorm_of_hasDirichletDensity
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:39:42.652879+00:00
-- url     : https://prove2.me/theorems/9c24f857-f5d0-42b7-b30e-c5c30adbd9be
-- title:
--   Bridge: exists prime abs Norm of has Dirichlet Density
-- statement:
--   The Bridge construction uses the exists prime abs Norm of has Dirichlet Density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean#L177-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/NeutralLocalFields/LocalFieldComparison/ExistsPrimeAbsNormOfHasDirichletDensity.lean#L177-L236

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

theorem ReciprocityTheory.Neutral.Bridge.exists_prime_absNorm_of_hasDirichletDensity {S : Set (HeightOneSpectrum (𝓞 K))} {δ : ℝ}
    (h : NumberField.Set.HasDirichletDensity S δ) (hδ : 0 < δ) {T : Set (HeightOneSpectrum (𝓞 K))} (hT : T.Finite) :
    ∃ 𝔭 ∈ S, 𝔭 ∉ T ∧ (Ideal.absNorm 𝔭.asIdeal).Prime := by sorry
