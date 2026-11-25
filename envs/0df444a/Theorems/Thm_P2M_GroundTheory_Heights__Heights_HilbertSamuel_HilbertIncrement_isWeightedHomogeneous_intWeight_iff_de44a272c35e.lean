-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_isWeightedHomogeneous_intWeight_iff_de44a272c35e
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_isWeightedHomogeneous_intWeight_iff_de44a272c35e
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:21:47.298073+00:00
-- url     : https://prove2.me/theorems/77056cee-5784-5d3f-96d7-4c6056b71bdf
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment is Weighted Homogeneous int Weight iff de44a272c35e: P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment is Weight
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment is Weighted Homogeneous int Weight iff de44a272c35e construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment is Weighted Homogeneous int Weight iff de44a272c35e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertIncrement.lean#L28-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertIncrement.lean#L28-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ColonSpanSingletonEqOfNotMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertIncrement
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
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.HilbertSamuel.HilbertIncrement
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_isWeightedHomogeneous_intWeight_iff_de44a272c35e {f : MRing ι F} {a : K → ℕ} :
    IsWeightedHomogeneous (intWeight (ι := ι)) f (fun k => (a k : ℤ)) ↔
      IsWeightedHomogeneous (blockWeight ι) f a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«HilbertIncrement».«isWeightedHomogeneous_intWeight_iff» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_isWeightedHomogeneous_intWeight_iff_de44a272c35e
