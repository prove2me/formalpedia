-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_homogeneousComponent_linear_mul_3e7d2fbc49db
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_homogeneousComponent_linear_mul_3e7d2fbc49db
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:08:56.702676+00:00
-- url     : https://prove2.me/theorems/abc4a013-af24-404d-aa9d-a0fa89c43c8b
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR homogeneous Component linear mul 3e7d2fbc49db: P2 M Ground Theory Heights  Heights Numbers DVR homogeneous Component linear mul 3e7d2fbc49db
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR homogeneous Component linear mul 3e7d2fbc49db construction uses the P2 M Ground Theory Heights  Heights Numbers DVR homogeneous Component linear mul 3e7d2fbc49db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L217-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PFlagIndependenceAlgebra.lean#L217-L238

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_homogeneousComponent_linear_mul_3e7d2fbc49db {σ : Type*} {L : MvPolynomial σ ℤ} (hL : L.IsHomogeneous 1)
    (P : MvPolynomial σ ℤ) (t : ℕ) :
    homogeneousComponent t (L * P) = if t = 0 then 0 else L * homogeneousComponent (t - 1) P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«homogeneousComponent_linear_mul» := P2M_GroundTheory_Heights__Heights_NumbersDVR_homogeneousComponent_linear_mul_3e7d2fbc49db
