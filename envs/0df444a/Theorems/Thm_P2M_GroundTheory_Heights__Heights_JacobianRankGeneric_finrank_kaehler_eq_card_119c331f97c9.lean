-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_JacobianRankGeneric_finrank_kaehler_eq_card_119c331f97c9
-- name    : P2M_GroundTheory_Heights__Heights_JacobianRankGeneric_finrank_kaehler_eq_card_119c331f97c9
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:46:16.898802+00:00
-- url     : https://prove2.me/theorems/5c64a180-4314-406b-9893-c36daaf94482
-- title:
--   P2 M Ground Theory Heights  Heights Jacobian Rank Generic finrank kaehler eq card 119c331f97c9: P2 M Ground Theory Heights  Heights Jacobian Rank Generic finrank kaehler eq card 119c331f97c9
-- statement:
--   The P2 M Ground Theory Heights  Heights Jacobian Rank Generic finrank kaehler eq card 119c331f97c9 construction uses the P2 M Ground Theory Heights  Heights Jacobian Rank Generic finrank kaehler eq card 119c331f97c9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PJacobianRankGeneric.lean#L26-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PJacobianRankGeneric.lean#L26-L58

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StJacobianRankGeneric
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PJacobianRankGeneric
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
noncomputable section
open MvPolynomial

theorem P2M_GroundTheory_Heights__Heights_JacobianRankGeneric_finrank_kaehler_eq_card_119c331f97c9 {k K : Type} [Field k] [Field K] [Algebra k K] (s : Finset K)
    (hs : IsTranscendenceBasis k ((↑) : s → K))
    (H : Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K) :
    Module.finrank K Ω[K⁄k] = s.card := by sorry

alias «GroundTheory».«Heights₂».«Heights».«JacobianRankGeneric».«finrank_kaehler_eq_card» := P2M_GroundTheory_Heights__Heights_JacobianRankGeneric_finrank_kaehler_eq_card_119c331f97c9
