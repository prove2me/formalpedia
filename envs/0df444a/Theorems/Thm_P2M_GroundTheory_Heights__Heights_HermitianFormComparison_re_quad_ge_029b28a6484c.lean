-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_ge_029b28a6484c
-- name    : P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_ge_029b28a6484c
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:18:11.494792+00:00
-- url     : https://prove2.me/theorems/97bd5e8f-4602-4b5a-87ee-c07c77b6985b
-- title:
--   P2 M Ground Theory Heights  Heights Hermitian Form Comparison re quad ge 029b28a6484c: P2 M Ground Theory Heights  Heights Hermitian Form Comparison re quad ge 029b28a6484c
-- statement:
--   The P2 M Ground Theory Heights  Heights Hermitian Form Comparison re quad ge 029b28a6484c construction uses the P2 M Ground Theory Heights  Heights Hermitian Form Comparison re quad ge 029b28a6484c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PHermFormCompare.lean#L54-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PHermFormCompare.lean#L54-L63

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

theorem P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_ge_029b28a6484c {n : ℕ} {N : Matrix (Fin n) (Fin n) ℂ} (hN : N.PosDef) (x : Fin n → ℂ) :
    (1 + ∑ k, (hN.1.eigenvalues k)⁻¹)⁻¹ * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ (N *ᵥ x)).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HermitianFormComparison».«re_quad_ge» := P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_ge_029b28a6484c
