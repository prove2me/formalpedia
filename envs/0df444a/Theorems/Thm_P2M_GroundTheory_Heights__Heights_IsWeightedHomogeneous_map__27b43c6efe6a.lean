-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsWeightedHomogeneous_map__27b43c6efe6a
-- name    : P2M_GroundTheory_Heights__Heights_IsWeightedHomogeneous_map__27b43c6efe6a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:34:21.866112+00:00
-- url     : https://prove2.me/theorems/3b6ebd3d-b96a-487e-9324-333bbf16890d
-- title:
--   P2 M Ground Theory Heights  Heights Is Weighted Homogeneous map  27b43c6efe6a: P2 M Ground Theory Heights  Heights Is Weighted Homogeneous map  27b43c6efe6a
-- statement:
--   The P2 M Ground Theory Heights  Heights Is Weighted Homogeneous map  27b43c6efe6a construction uses the P2 M Ground Theory Heights  Heights Is Weighted Homogeneous map  27b43c6efe6a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/LowerBoundConditional.lean#L69-L74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
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
open MvPolynomial MeasureTheory NumberField
noncomputable section
variable {R : Type*} [CommRing R]
variable {k n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IsWeightedHomogeneous_map__27b43c6efe6a {σ S : Type*} [CommSemiring S] {w : σ → ℕ} {f : MvPolynomial σ R}
    {m : ℕ} (hf : IsWeightedHomogeneous w f m) (φ : R →+* S) :
    IsWeightedHomogeneous w (MvPolynomial.map φ f) m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IsWeightedHomogeneous».«map'» := P2M_GroundTheory_Heights__Heights_IsWeightedHomogeneous_map__27b43c6efe6a
