-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_weight_intWeight_8853f7eb7b24
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_weight_intWeight_8853f7eb7b24
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:08:35.375052+00:00
-- url     : https://prove2.me/theorems/225610b6-9552-4634-be34-4f9f1e7d3b98
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment weight int Weight 8853f7eb7b24: P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment weight int Weight 8853f7eb7b24
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment weight int Weight 8853f7eb7b24 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Hilbert Increment weight int Weight 8853f7eb7b24 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertIncrement.lean#L19-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PHilbertIncrement.lean#L19-L26

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_weight_intWeight_8853f7eb7b24 (e : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (intWeight (ι := ι)) e =
      fun k => ((Finsupp.weight (blockWeight ι) e k : ℕ) : ℤ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«HilbertIncrement».«weight_intWeight» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_HilbertIncrement_weight_intWeight_8853f7eb7b24
