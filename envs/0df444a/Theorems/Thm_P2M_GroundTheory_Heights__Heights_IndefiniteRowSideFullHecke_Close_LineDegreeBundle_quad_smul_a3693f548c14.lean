-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_quad_smul_a3693f548c14
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_quad_smul_a3693f548c14
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:21:41.039869+00:00
-- url     : https://prove2.me/theorems/934f8767-9b43-42f5-b4d0-559e11891004
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Degree Bundle quad smul a3693f548c14: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Degree
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Degree Bundle quad smul a3693f548c14 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Close Line Degree Bundle quad smul a3693f548c14 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLineDegreeBundle.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PLineDegreeBundle.lean#L48-L51

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_quad_smul_a3693f548c14 {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) (u : Fin n → ℂ) :
    star (z • u) ⬝ᵥ (H *ᵥ (z • u)) = (star z * z) * (star u ⬝ᵥ (H *ᵥ u)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Close».«LineDegreeBundle».«quad_smul» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_LineDegreeBundle_quad_smul_a3693f548c14
