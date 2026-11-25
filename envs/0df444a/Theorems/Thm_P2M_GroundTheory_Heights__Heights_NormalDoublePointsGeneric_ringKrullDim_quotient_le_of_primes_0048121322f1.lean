-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_ringKrullDim_quotient_le_of_primes_0048121322f1
-- name    : P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_ringKrullDim_quotient_le_of_primes_0048121322f1
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:08.074952+00:00
-- url     : https://prove2.me/theorems/b950692a-02ed-48a1-b44f-933855256eae
-- title:
--   P2 M Ground Theory Heights  Heights Normal Double Points Generic ring Krull Dim quotient le of primes 0048121322f1: P2 M Ground Theory Heights  Heights Normal Double Points Generic ring Krull Dim quot
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Double Points Generic ring Krull Dim quotient le of primes 0048121322f1 construction uses the P2 M Ground Theory Heights  Heights Normal Double Points Generic ring Krull Dim quotient le of primes 0048121322f1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalDoublePointsGeneric.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalDoublePointsGeneric.lean#L13-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalDoublePointsGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PNormalDoublePointsGeneric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Topology ComplexSets
noncomputable section
open GroundTheory.Heights₂.Heights.NormalDoublePointsGeneric

theorem P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_ringKrullDim_quotient_le_of_primes_0048121322f1 {R : Type*} [CommRing R] (I : Ideal R) (k : WithBot ℕ∞)
    (h : ∀ W : Ideal R, W.IsPrime → I ≤ W → ∃ K : Ideal R, K ≤ W ∧ ringKrullDim (R ⧸ K) ≤ k) :
    ringKrullDim (R ⧸ I) ≤ k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalDoublePointsGeneric».«ringKrullDim_quotient_le_of_primes» := P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_ringKrullDim_quotient_le_of_primes_0048121322f1
