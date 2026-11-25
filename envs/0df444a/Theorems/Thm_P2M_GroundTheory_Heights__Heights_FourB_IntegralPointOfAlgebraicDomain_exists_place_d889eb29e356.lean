-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_exists_place_d889eb29e356
-- name    : P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_exists_place_d889eb29e356
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:46:01.684381+00:00
-- url     : https://prove2.me/theorems/654426ed-00dd-48ea-8985-fbab9c52913a
-- title:
--   P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Domain exists place d889eb29e356: P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Domain exists place d889
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Domain exists place d889eb29e356 construction uses the P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Domain exists place d889eb29e356 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PIntegralPointOfAlgebraicDomain.lean#L83-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PIntegralPointOfAlgebraicDomain.lean#L83-L136

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsIntegralPointAlgebraic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_NormLeOneIffIsIntegralElemOfEquiv
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PIntegralPointOfAlgebraicDomain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.IntegralPointOfAlgebraicDomain
variable {K : Type*} [Field K] {S : Type*} [CommRing S]
  [Algebra S K] [IsFractionRing S K] (M : Ideal S) [M.IsMaximal]

theorem P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_exists_place_d889eb29e356 [NumberField K] (x₀ : 𝓞 K) (hx₀ : x₀ ≠ 0) (s₀ : S) (hs₀ : s₀ ∈ M)
    (h₀ : algebraMap S K s₀ = algebraMap (𝓞 K) K x₀) :
    ∃ w : HeightOneSpectrum (𝓞 K), (∀ s : S, w.valuation K (algebraMap S K s) ≤ 1) ∧
      ∀ s ∈ M, w.valuation K (algebraMap S K s) < 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«IntegralPointOfAlgebraicDomain».«exists_place» := P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_exists_place_d889eb29e356
