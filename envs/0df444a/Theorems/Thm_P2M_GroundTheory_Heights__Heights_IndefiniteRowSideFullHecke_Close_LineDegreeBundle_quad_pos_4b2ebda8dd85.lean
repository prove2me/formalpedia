-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_quad_pos_4b2ebda8dd85
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_quad_pos_4b2ebda8dd85
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:55.223232+00:00
-- url     : https://prove2.me/theorems/2051c4a5-2929-42b7-8fc8-0ee0d61f54d5
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Degree Bundle quad pos 4b2ebda8dd85: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Degree
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Degree Bundle quad pos 4b2ebda8dd85 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Degree Bundle quad pos 4b2ebda8dd85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLineDegreeBundle.lean#L53-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLineDegreeBundle.lean#L53-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_LineDegreeBundleStatement
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PointHeightDegreeHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PLineDegreeBundle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open NumberField Matrix TensorProduct ComplexAt
open scoped ComplexOrder nonZeroDivisors
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_quad_pos_4b2ebda8dd85 {n : ℕ} {H : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosDef) {u : Fin n → ℂ}
    (hu : u ≠ 0) :
    ‖star u ⬝ᵥ (H *ᵥ u)‖ = (star u ⬝ᵥ (H *ᵥ u)).re ∧ 0 < (star u ⬝ᵥ (H *ᵥ u)).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«LineDegreeBundle».«quad_pos» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_quad_pos_4b2ebda8dd85
