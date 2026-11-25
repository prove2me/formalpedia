-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MultiHomogMemCoordinate_cone_monomial_1e7c61cf30d8
-- name    : P2M_GroundTheory_Heights__Heights_MultiHomogMemCoordinate_cone_monomial_1e7c61cf30d8
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:06:42.492384+00:00
-- url     : https://prove2.me/theorems/800fa3aa-a001-5cac-8c3c-d4fbf4fe24b3
-- title:
--   P2 M Ground Theory Heights  Heights Multi Homog Mem Coordinate cone monomial 1e7c61cf30d8: P2 M Ground Theory Heights  Heights Multi Homog Mem Coordinate cone monomial 1e7c61cf30d8
-- statement:
--   The P2 M Ground Theory Heights  Heights Multi Homog Mem Coordinate cone monomial 1e7c61cf30d8 construction uses the P2 M Ground Theory Heights  Heights Multi Homog Mem Coordinate cone monomial 1e7c61cf30d8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PMultiHomogMemCoord.lean#L23-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PMultiHomogMemCoord.lean#L23-L34

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PMultiHomogMemCoord
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial
open GroundTheory.Heights₂.Heights.MultiHomogMemCoordinate
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem P2M_GroundTheory_Heights__Heights_MultiHomogMemCoordinate_cone_monomial_1e7c61cf30d8 (y : (Σ k, ι k) → Ω) (m : (Σ k, ι k) →₀ ℕ) (c : ℤ) (a : K → ℕ)
    (hm : ∀ k, ∑ i, m ⟨k, i⟩ = a k) :
    mConeMap y (monomial m c) =
      C (aeval y (monomial m c)) * monomial (Finsupp.equivFunOnFinite.symm a) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MultiHomogMemCoordinate».«cone_monomial» := P2M_GroundTheory_Heights__Heights_MultiHomogMemCoordinate_cone_monomial_1e7c61cf30d8
