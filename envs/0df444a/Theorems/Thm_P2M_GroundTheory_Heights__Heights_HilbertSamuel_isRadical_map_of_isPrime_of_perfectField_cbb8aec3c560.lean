-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_isRadical_map_of_isPrime_of_perfectField_cbb8aec3c560
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_isRadical_map_of_isPrime_of_perfectField_cbb8aec3c560
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:18:57.815+00:00
-- url     : https://prove2.me/theorems/727321fb-7a33-5074-986c-2d483c2e5c61
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel is Radical map of is Prime of perfect Field cbb8aec3c560: P2 M Ground Theory Heights  Heights Hilbert Samuel is Radical map of is Prime of perfect Fi
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel is Radical map of is Prime of perfect Field cbb8aec3c560 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel is Radical map of is Prime of perfect Field cbb8aec3c560 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPrimeComplexRadical.lean#L74-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPrimeComplexRadical.lean#L74-L91

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsPrimeComplexRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PPrimeComplexRadical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial TensorProduct
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_isRadical_map_of_isPrime_of_perfectField_cbb8aec3c560 (K F : Type*) [Field K] [PerfectField K]
    [Field F] [Algebra K F] (σ : Type*) [Fintype σ] (Q : Ideal (MvPolynomial σ K))
    [Q.IsPrime] : (Q.map (MvPolynomial.map (algebraMap K F))).IsRadical := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«isRadical_map_of_isPrime_of_perfectField» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_isRadical_map_of_isPrime_of_perfectField_cbb8aec3c560
