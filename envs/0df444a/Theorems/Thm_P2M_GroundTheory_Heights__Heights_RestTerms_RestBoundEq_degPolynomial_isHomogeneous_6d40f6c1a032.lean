-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_degPolynomial_isHomogeneous_6d40f6c1a032
-- name    : P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_degPolynomial_isHomogeneous_6d40f6c1a032
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:20:32.917743+00:00
-- url     : https://prove2.me/theorems/0089bb31-d1be-50e5-b514-c8b580b2c5ea
-- title:
--   P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq deg Polynomial is Homogeneous 6d40f6c1a032: P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq deg Polynomial is Homogeneous 6d40
-- statement:
--   The P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq deg Polynomial is Homogeneous 6d40f6c1a032 construction uses the P2 M Ground Theory Heights  Heights Rest Terms Rest Bound Eq deg Polynomial is Homogeneous 6d40f6c1a032 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/DegPolynomialIsHomogeneous.lean#L67-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/DegPolynomialIsHomogeneous.lean#L67-L88

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsPowerSumDecompositionHomogeneousComponent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PRestPolynomialHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PVandermondeOfHomogeneous
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_DegPolynomialIsHomogeneous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial Finset
noncomputable section
open GroundTheory.Heights₂.Heights.RestTerms.RestBoundEq

theorem P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_degPolynomial_isHomogeneous_6d40f6c1a032 (f r a : ℕ) (c : SmallBlock) :
    (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c).IsHomogeneous
      (topDegree f (r + a)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RestTerms».«RestBoundEq».«degPolynomial_isHomogeneous» := P2M_GroundTheory_Heights__Heights_RestTerms_RestBoundEq_degPolynomial_isHomogeneous_6d40f6c1a032
