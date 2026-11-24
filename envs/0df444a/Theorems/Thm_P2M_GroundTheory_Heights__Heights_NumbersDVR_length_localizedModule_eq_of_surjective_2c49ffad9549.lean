-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedModule_eq_of_surjective_2c49ffad9549
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedModule_eq_of_surjective_2c49ffad9549
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:21:54.005473+00:00
-- url     : https://prove2.me/theorems/ed5ea31b-330e-4ed5-b8d7-07ba7913955d
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR length localized Module eq of surjective 2c49ffad9549: P2 M Ground Theory Heights  Heights Numbers DVR length localized Module eq of surjective 2c49ffad
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR length localized Module eq of surjective 2c49ffad9549 construction uses the P2 M Ground Theory Heights  Heights Numbers DVR length localized Module eq of surjective 2c49ffad9549 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpecialMultAt.lean#L13-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PSpecialMultAt.lean#L13-L80

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialMultAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedModule_eq_of_surjective_2c49ffad9549 {S T : Type*} [CommRing S] [CommRing T]
    (π : S →+* T) (hπ : Function.Surjective π) (Q : Ideal T) [Q.IsPrime] (W : Ideal S) [W.IsPrime]
    (hW : W = Q.comap π) (M N : Type*) [AddCommGroup M] [Module S M] [AddCommGroup N] [Module T N]
    (e : M ≃+ N) (he : ∀ (s : S) (x : M), e (s • x) = π s • e x) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M) =
      Module.length (Localization.AtPrime Q) (LocalizedModule Q.primeCompl N) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«length_localizedModule_eq_of_surjective» := P2M_GroundTheory_Heights__Heights_NumbersDVR_length_localizedModule_eq_of_surjective_2c49ffad9549
