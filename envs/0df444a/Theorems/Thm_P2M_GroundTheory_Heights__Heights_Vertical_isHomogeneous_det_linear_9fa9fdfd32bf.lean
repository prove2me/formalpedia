-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_isHomogeneous_det_linear_9fa9fdfd32bf
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_isHomogeneous_det_linear_9fa9fdfd32bf
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:29.688838+00:00
-- url     : https://prove2.me/theorems/6ba74c78-d469-42cb-b0a7-f7cfc526ce1c
-- title:
--   P2 M Ground Theory Heights  Heights Vertical is Homogeneous det linear 9fa9fdfd32bf: P2 M Ground Theory Heights  Heights Vertical is Homogeneous det linear 9fa9fdfd32bf
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical is Homogeneous det linear 9fa9fdfd32bf construction uses the P2 M Ground Theory Heights  Heights Vertical is Homogeneous det linear 9fa9fdfd32bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChowSecDegree.lean#L41-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChowSecDegree.lean#L41-L49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PNormFormEval
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChowSecDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_Vertical_isHomogeneous_det_linear_9fa9fdfd32bf {R : Type*} [CommRing R] {σ ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : Matrix ι ι (MvPolynomial σ R)) (hN : ∀ i k, (N i k).IsHomogeneous 1) :
    N.det.IsHomogeneous (Fintype.card ι) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«isHomogeneous_det_linear» := P2M_GroundTheory_Heights__Heights_Vertical_isHomogeneous_det_linear_9fa9fdfd32bf
