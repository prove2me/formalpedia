-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_le_07935f5f434a
-- name    : P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_le_07935f5f434a
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:07.010327+00:00
-- url     : https://prove2.me/theorems/a4a58b98-6875-4db3-901e-c8fa7ff239d9
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Form Comparison re quad le 07935f5f434a: P2 M Ground Theory Heights  Heights Hermitian Form Comparison re quad le 07935f5f434a
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Form Comparison re quad le 07935f5f434a construction uses the P2 M Ground Theory Heights  Heights Hermitian Form Comparison re quad le 07935f5f434a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PHermFormCompare.lean#L46-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PHermFormCompare.lean#L46-L52

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

theorem P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_le_07935f5f434a {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (M *ᵥ x)).re ≤ (1 + ∑ k, hM.1.eigenvalues k) * (star x ⬝ᵥ x).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianFormComparison».«re_quad_le» := P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_le_07935f5f434a
