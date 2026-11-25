-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_finiteDimensional_affField_410254da17a8
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_finiteDimensional_affField_410254da17a8
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:22:01.656697+00:00
-- url     : https://prove2.me/theorems/85280ab5-43dc-5f0d-b084-2537565e8dbf
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Hilbert Point finite Dimensional aff Field 410254da17a8: P2 M Ground Theory Heights  Heights Kleiman Hilbert Point finite Dimensional aff Field 410254da17a8
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Hilbert Point finite Dimensional aff Field 410254da17a8 construction uses the P2 M Ground Theory Heights  Heights Kleiman Hilbert Point finite Dimensional aff Field 410254da17a8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L110-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L110-L120

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_finiteDimensional_affField_410254da17a8 (hy : IsSubvar y (primeOf (S := k) y) 0) (hj : y j ≠ 0) :
    FiniteDimensional k ((affRing k y j).toIntermediateField' (isField_affRing hy hj)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«HilbertPoint».«finiteDimensional_affField» := P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_finiteDimensional_affField_410254da17a8
