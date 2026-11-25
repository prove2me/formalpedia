-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_homog_of_mem_minimalPrimes_29f5b41f0987
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_homog_of_mem_minimalPrimes_29f5b41f0987
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:59:21.888324+00:00
-- url     : https://prove2.me/theorems/6dcd14ef-b2cc-44c1-9227-f5e8671fa37d
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Step Three On W Gen homog of mem minimal Primes 29f5b41f0987: P2 M Ground Theory Heights  Heights Kleiman Step Three On W Gen homog of mem minimal Primes 29
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Step Three On W Gen homog of mem minimal Primes 29f5b41f0987 construction uses the P2 M Ground Theory Heights  Heights Kleiman Step Three On W Gen homog of mem minimal Primes 29f5b41f0987 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWGen.lean#L50-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PStepThreeOnWGen.lean#L50-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeOnWGen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrictGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_RestrLenRestrictSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepDataJProper
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSubvarDrop
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PPrimeFiltrationRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PGenerated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeOnWGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.StepThree GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW GroundTheory.Heights₂.Heights.Kleiman.StepThree.OnW.Gen
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
attribute [local instance] MvPolynomial.gradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_homog_of_mem_minimalPrimes_29f5b41f0987 (D : SubSystem S x Ω) (s : Ω) {pp : Ideal (Poly S N)}
    (hpp : pp ∈ (zeroIdeal D s).minimalPrimes) :
    ∀ p ∈ pp, ∀ d : ℕ, homogeneousComponent d p ∈ pp := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«StepThree».«OnW».«Gen».«homog_of_mem_minimalPrimes» := P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_OnW_Gen_homog_of_mem_minimalPrimes_29f5b41f0987
