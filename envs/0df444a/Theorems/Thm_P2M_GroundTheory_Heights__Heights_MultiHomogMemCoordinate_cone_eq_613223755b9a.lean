-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_MultiHomogMemCoordinate_cone_eq_613223755b9a
-- name    : P2M_GroundTheory_Heights__Heights_MultiHomogMemCoordinate_cone_eq_613223755b9a
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:17.409797+00:00
-- url     : https://prove2.me/theorems/36551814-a3a3-49d8-994c-f4626790f54c
-- title:
--   P2 M Ground Theory Heights  Heights Multi Homog Mem Coordinate cone eq 613223755b9a: P2 M Ground Theory Heights  Heights Multi Homog Mem Coordinate cone eq 613223755b9a
-- statement:
--   The P2 M Ground Theory Heights  Heights Multi Homog Mem Coordinate cone eq 613223755b9a construction uses the P2 M Ground Theory Heights  Heights Multi Homog Mem Coordinate cone eq 613223755b9a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PMultiHomogMemCoord.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PMultiHomogMemCoord.lean#L36-L41

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

theorem P2M_GroundTheory_Heights__Heights_MultiHomogMemCoordinate_cone_eq_613223755b9a (y : (Σ k, ι k) → Ω) (g : MRing ι) (a : K → ℕ) (hg : IsMultiHomog g a) :
    mConeMap y g = C (aeval y g) * monomial (Finsupp.equivFunOnFinite.symm a) 1 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«MultiHomogMemCoordinate».«cone_eq» := P2M_GroundTheory_Heights__Heights_MultiHomogMemCoordinate_cone_eq_613223755b9a
