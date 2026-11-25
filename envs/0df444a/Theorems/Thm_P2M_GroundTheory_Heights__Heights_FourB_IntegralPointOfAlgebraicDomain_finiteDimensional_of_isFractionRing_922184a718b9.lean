-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_finiteDimensional_of_isFractionRing_922184a718b9
-- name    : P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_finiteDimensional_of_isFractionRing_922184a718b9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T13:01:06.488024+00:00
-- url     : https://prove2.me/theorems/8c2b5e92-151d-5ff4-a17e-b456887f80f7
-- title:
--   P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Domain finite Dimensional of is Fraction Ring 922184a718b9: P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebrai
-- statement:
--   The P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Domain finite Dimensional of is Fraction Ring 922184a718b9 construction uses the P2 M Ground Theory Heights  Heights Four B Integral Point Of Algebraic Domain finite Dimensional of is Fraction Ring 922184a718b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PIntegralPointOfAlgebraicDomain.lean#L22-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/PIntegralPointOfAlgebraicDomain.lean#L22-L50

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
variable {F : Type*} [Field F] [NumberField F] {S : Type*} [CommRing S]
  [Algebra (𝓞 F) S] {K : Type*} [Field K] [Algebra S K] [IsFractionRing S K] [Algebra F K]

theorem P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_finiteDimensional_of_isFractionRing_922184a718b9 [Algebra.FiniteType (𝓞 F) S]
    [Algebra.IsAlgebraic (𝓞 F) S]
    (hc : ∀ r : 𝓞 F, algebraMap F K (algebraMap (𝓞 F) F r) = algebraMap S K (algebraMap (𝓞 F) S r)) :
    FiniteDimensional F K := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FourB».«IntegralPointOfAlgebraicDomain».«finiteDimensional_of_isFractionRing» := P2M_GroundTheory_Heights__Heights_FourB_IntegralPointOfAlgebraicDomain_finiteDimensional_of_isFractionRing_922184a718b9
