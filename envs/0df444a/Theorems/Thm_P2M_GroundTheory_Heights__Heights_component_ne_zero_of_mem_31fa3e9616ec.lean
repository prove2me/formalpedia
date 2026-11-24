-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_component_ne_zero_of_mem_31fa3e9616ec
-- name    : P2M_GroundTheory_Heights__Heights_component_ne_zero_of_mem_31fa3e9616ec
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:28:05.74668+00:00
-- url     : https://prove2.me/theorems/87864711-60cc-4506-bd94-fa81c73999b9
-- title:
--   P2 M Ground Theory Heights  Heights component ne zero of mem 31fa3e9616ec: P2 M Ground Theory Heights  Heights component ne zero of mem 31fa3e9616ec
-- statement:
--   The P2 M Ground Theory Heights  Heights component ne zero of mem 31fa3e9616ec construction uses the P2 M Ground Theory Heights  Heights component ne zero of mem 31fa3e9616ec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L36-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L36-L43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
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
open MvPolynomial
noncomputable section
variable {R σ : Type*} [CommRing R] {w : σ → ℕ}

theorem P2M_GroundTheory_Heights__Heights_component_ne_zero_of_mem_31fa3e9616ec {p : MvPolynomial σ R} {a : ℕ} (ha : a ∈ weightSet w p) :
    weightedHomogeneousComponent w a p ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«component_ne_zero_of_mem» := P2M_GroundTheory_Heights__Heights_component_ne_zero_of_mem_31fa3e9616ec
