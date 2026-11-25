-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_ringKrullDim_quot_sup_span_add_one_le_1de9644a92aa
-- name    : P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_ringKrullDim_quot_sup_span_add_one_le_1de9644a92aa
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:05:04.262215+00:00
-- url     : https://prove2.me/theorems/0288d836-7194-4d97-94aa-b36656db6633
-- title:
--   P2 M Ground Theory Heights  Heights Normal Double Points Generic ring Krull Dim quot sup span add one le 1de9644a92aa: P2 M Ground Theory Heights  Heights Normal Double Points Generic ring Krull Dim q
-- statement:
--   The P2 M Ground Theory Heights  Heights Normal Double Points Generic ring Krull Dim quot sup span add one le 1de9644a92aa construction uses the P2 M Ground Theory Heights  Heights Normal Double Points Generic ring Krull Dim quot sup span add one le 1de9644a92aa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalDoublePointsGeneric.lean#L31-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PNormalDoublePointsGeneric.lean#L31-L41

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

theorem P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_ringKrullDim_quot_sup_span_add_one_le_1de9644a92aa {n : ℕ} (p : Ideal (MvPolynomial (Fin n) ℂ)) [p.IsPrime]
    {g : MvPolynomial (Fin n) ℂ} (hg : g ∉ p) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ (p ⊔ Ideal.span {g})) + 1 ≤
      ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NormalDoublePointsGeneric».«ringKrullDim_quot_sup_span_add_one_le» := P2M_GroundTheory_Heights__Heights_NormalDoublePointsGeneric_ringKrullDim_quot_sup_span_add_one_le_1de9644a92aa
