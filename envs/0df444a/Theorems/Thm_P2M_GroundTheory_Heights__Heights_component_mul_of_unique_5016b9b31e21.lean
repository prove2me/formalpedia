-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_component_mul_of_unique_5016b9b31e21
-- name    : P2M_GroundTheory_Heights__Heights_component_mul_of_unique_5016b9b31e21
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:44:43.953196+00:00
-- url     : https://prove2.me/theorems/48b939c8-ad7e-4daa-97e1-bd7bb6a188a1
-- title:
--   P2 M Ground Theory Heights  Heights component mul of unique 5016b9b31e21: P2 M Ground Theory Heights  Heights component mul of unique 5016b9b31e21
-- statement:
--   The P2 M Ground Theory Heights  Heights component mul of unique 5016b9b31e21 construction uses the P2 M Ground Theory Heights  Heights component mul of unique 5016b9b31e21 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L45-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/ChowDegree.lean#L45-L96

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

theorem P2M_GroundTheory_Heights__Heights_component_mul_of_unique_5016b9b31e21 (p q : MvPolynomial σ R) (a b : ℕ)
    (h : ∀ a' ∈ weightSet w p, ∀ b' ∈ weightSet w q, a' + b' = a + b → a' = a ∧ b' = b) :
    weightedHomogeneousComponent w (a + b) (p * q) =
      weightedHomogeneousComponent w a p * weightedHomogeneousComponent w b q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«component_mul_of_unique» := P2M_GroundTheory_Heights__Heights_component_mul_of_unique_5016b9b31e21
