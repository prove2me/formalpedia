-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_div_mem_affRing_of_mem_twistMod_32809b3bdbde
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_div_mem_affRing_of_mem_twistMod_32809b3bdbde
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:58:26.436531+00:00
-- url     : https://prove2.me/theorems/6d750b45-e8fd-4b5a-a02b-4d73a485714f
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Hilbert Point div mem aff Ring of mem twist Mod 32809b3bdbde: P2 M Ground Theory Heights  Heights Kleiman Hilbert Point div mem aff Ring of mem twist Mod 32
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Hilbert Point div mem aff Ring of mem twist Mod 32809b3bdbde construction uses the P2 M Ground Theory Heights  Heights Kleiman Hilbert Point div mem aff Ring of mem twist Mod 32809b3bdbde property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L190-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PHilbertPoint.lean#L190-L214

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

theorem P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_div_mem_affRing_of_mem_twistMod_32809b3bdbde (hj : y j ≠ 0) (n : ℕ) {z : Ω}
    (hz : z ∈ twistMod k y (n : ℤ) (singleChart hj)) : z / y j ^ n ∈ affRing k y j := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«HilbertPoint».«div_mem_affRing_of_mem_twistMod» := P2M_GroundTheory_Heights__Heights_Kleiman_HilbertPoint_div_mem_affRing_of_mem_twistMod_32809b3bdbde
