-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_totalDegree_add_card_le_ringKrullDim_97857621ed3a
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_totalDegree_add_card_le_ringKrullDim_97857621ed3a
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:19:25.463869+00:00
-- url     : https://prove2.me/theorems/ba8876b8-0e76-56ac-90f6-e9905586be18
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers total Degree add card le ring Krull Dim 97857621ed3a: P2 M Ground Theory Heights  Heights Field Numbers total Degree add card le ring Krull Dim 978576
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers total Degree add card le ring Krull Dim 97857621ed3a construction uses the P2 M Ground Theory Heights  Heights Field Numbers total Degree add card le ring Krull Dim 97857621ed3a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbDegreeBound.lean#L84-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbDegreeBound.lean#L84-L210

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_StatementsDegreeBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbDegreeBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_totalDegree_add_card_le_ringKrullDim_97857621ed3a (h1 : HilbEventuallyPoly.Statement.{u})
    (h2 : HilbExactDivide.Statement.{u}) (h3 : PolyOfDiffs.Statement)
    (h4 : PrimeFiltration.Statement.{u}) (hU : EventuallyPolyUnique.Statement)
    (hS : EventuallyPolyShift.Statement) (hZ : HilbIrrelevantZero.Statement.{u})
    (hD : RelevantPrimeDimGe.Statement.{u})
    (F : Type u) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (n : ℕ) :
    ∀ I : Ideal (MRing ι F), IsMultiHomogIdeal I → ringKrullDim (MRing ι F ⧸ I) < n →
      ∀ p : MvPolynomial K ℚ, EventuallyPoly (hilbFn I) p → p ≠ 0 →
      ((p.totalDegree + Fintype.card K : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MRing ι F ⧸ I) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«totalDegree_add_card_le_ringKrullDim» := P2M_GroundTheory_Heights__Heights_FieldNumbers_totalDegree_add_card_le_ringKrullDim_97857621ed3a
