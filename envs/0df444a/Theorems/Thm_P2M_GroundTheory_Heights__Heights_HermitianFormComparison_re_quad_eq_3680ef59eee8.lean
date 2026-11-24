-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_eq_3680ef59eee8
-- name    : P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_eq_3680ef59eee8
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T01:07:55.540518+00:00
-- url     : https://prove2.me/theorems/cfeb5d00-2fc5-466b-a4e8-4a287a88d59e
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Form Comparison re quad eq 3680ef59eee8: P2 M Ground Theory Heights  Heights Hermitian Form Comparison re quad eq 3680ef59eee8
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Form Comparison re quad eq 3680ef59eee8 construction uses the P2 M Ground Theory Heights  Heights Hermitian Form Comparison re quad eq 3680ef59eee8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PHermFormCompare.lean#L22-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PHermFormCompare.lean#L22-L39

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
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
open Matrix
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.HermitianFormComparison

theorem P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_eq_3680ef59eee8 {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (A *ᵥ x)).re = ∑ k, hA.eigenvalues k *
      ‖(star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ x) k‖ ^ 2 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianFormComparison».«re_quad_eq» := P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_eq_3680ef59eee8
