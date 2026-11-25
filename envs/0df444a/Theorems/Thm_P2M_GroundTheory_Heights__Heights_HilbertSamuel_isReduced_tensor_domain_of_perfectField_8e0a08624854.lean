-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_isReduced_tensor_domain_of_perfectField_8e0a08624854
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_isReduced_tensor_domain_of_perfectField_8e0a08624854
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:19:15.048093+00:00
-- url     : https://prove2.me/theorems/f2706043-89ba-4b4f-8da5-f39e464b3fbc
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel is Reduced tensor domain of perfect Field 8e0a08624854: P2 M Ground Theory Heights  Heights Hilbert Samuel is Reduced tensor domain of perfect Field
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel is Reduced tensor domain of perfect Field 8e0a08624854 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel is Reduced tensor domain of perfect Field 8e0a08624854 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPrimeComplexRadical.lean#L61-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PPrimeComplexRadical.lean#L61-L72

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_isReduced_tensor_domain_of_perfectField_8e0a08624854 (K A F : Type*) [Field K] [PerfectField K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Field F] [Algebra K F] :
    IsReduced (F ⊗[K] A) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«isReduced_tensor_domain_of_perfectField» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_isReduced_tensor_domain_of_perfectField_8e0a08624854
