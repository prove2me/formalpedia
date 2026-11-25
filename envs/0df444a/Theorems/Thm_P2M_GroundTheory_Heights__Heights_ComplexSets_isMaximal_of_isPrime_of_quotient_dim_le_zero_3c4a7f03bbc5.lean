-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_isMaximal_of_isPrime_of_quotient_dim_le_zero_3c4a7f03bbc5
-- name    : P2M_GroundTheory_Heights__Heights_ComplexSets_isMaximal_of_isPrime_of_quotient_dim_le_zero_3c4a7f03bbc5
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:16:35.112162+00:00
-- url     : https://prove2.me/theorems/3a747167-ce3b-4eed-89c3-4de81d16d7df
-- title:
--   P2 M Ground Theory Heights  Heights Complex Sets is Maximal of is Prime of quotient dim le zero 3c4a7f03bbc5: P2 M Ground Theory Heights  Heights Complex Sets is Maximal of is Prime of quotient dim le
-- statement:
--   The P2 M Ground Theory Heights  Heights Complex Sets is Maximal of is Prime of quotient dim le zero 3c4a7f03bbc5 construction uses the P2 M Ground Theory Heights  Heights Complex Sets is Maximal of is Prime of quotient dim le zero 3c4a7f03bbc5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHomogDimZeroPow.lean#L25-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PHomogDimZeroPow.lean#L25-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHomogDimZeroPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHomogDimZeroPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ComplexSets
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.gradedAlgebra

theorem P2M_GroundTheory_Heights__Heights_ComplexSets_isMaximal_of_isPrime_of_quotient_dim_le_zero_3c4a7f03bbc5 {R : Type*} [CommRing R] {K Q : Ideal R}
    (hK : ringKrullDim (R ⧸ K) ≤ 0) (hQ : Q.IsPrime) (hKQ : K ≤ Q) : Q.IsMaximal := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ComplexSets».«isMaximal_of_isPrime_of_quotient_dim_le_zero» := P2M_GroundTheory_Heights__Heights_ComplexSets_isMaximal_of_isPrime_of_quotient_dim_le_zero_3c4a7f03bbc5
