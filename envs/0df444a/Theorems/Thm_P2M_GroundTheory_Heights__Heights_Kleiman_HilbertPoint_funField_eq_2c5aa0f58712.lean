-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_funField_eq_2c5aa0f58712
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_funField_eq_2c5aa0f58712
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:56:10.310595+00:00
-- url     : https://prove2.me/theorems/d96dc7f7-ba22-43d6-92c6-e412edf45be3
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Hilbert Point fun Field eq 2c5aa0f58712: P2 M Ground Theory Heights  Heights Kleiman Hilbert Point fun Field eq 2c5aa0f58712
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Hilbert Point fun Field eq 2c5aa0f58712 construction uses the P2 M Ground Theory Heights  Heights Kleiman Hilbert Point fun Field eq 2c5aa0f58712 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L92-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L92-L108

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PHilbertPoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.HilbertPoint
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
variable {y : Fin (N + 1) → Ω} {j : Fin (N + 1)}

theorem P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_funField_eq_2c5aa0f58712 (hj : y j ≠ 0) (hF : IsField (affRing k y j)) :
    funField (k := k) y = (affRing k y j).toIntermediateField' hF := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«HilbertPoint».«funField_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_funField_eq_2c5aa0f58712
