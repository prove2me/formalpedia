-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MultiHomogMemCoordinate_mapDomain_fst_eq_d16f83d8ff63
-- name    : P2M_GroundTheory_Heights__Heights_MultiHomogMemCoordinate_mapDomain_fst_eq_d16f83d8ff63
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:04:33.36081+00:00
-- url     : https://prove2.me/theorems/02b2b4f9-5a23-42ad-9cad-7b0bc5d69a68
-- title:
--   P2 M Ground Theory Heights  Heights Multi Homog Mem Coordinate map Domain fst eq d16f83d8ff63: P2 M Ground Theory Heights  Heights Multi Homog Mem Coordinate map Domain fst eq d16f83d8ff63
-- statement:
--   The P2 M Ground Theory Heights  Heights Multi Homog Mem Coordinate map Domain fst eq d16f83d8ff63 construction uses the P2 M Ground Theory Heights  Heights Multi Homog Mem Coordinate map Domain fst eq d16f83d8ff63 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PMultiHomogMemCoord.lean#L13-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PMultiHomogMemCoord.lean#L13-L21

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

theorem P2M_GroundTheory_Heights__Heights_MultiHomogMemCoordinate_mapDomain_fst_eq_d16f83d8ff63 (m : (Σ k, ι k) →₀ ℕ) (a : K → ℕ) (hm : ∀ k, ∑ i, m ⟨k, i⟩ = a k) :
    Finsupp.mapDomain Sigma.fst m = Finsupp.equivFunOnFinite.symm a := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MultiHomogMemCoordinate».«mapDomain_fst_eq» := P2M_GroundTheory_Heights__Heights_MultiHomogMemCoordinate_mapDomain_fst_eq_d16f83d8ff63
