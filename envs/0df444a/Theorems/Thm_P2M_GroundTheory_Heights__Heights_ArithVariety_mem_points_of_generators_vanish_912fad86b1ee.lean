-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_of_generators_vanish_912fad86b1ee
-- name    : P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_of_generators_vanish_912fad86b1ee
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:15:20.950515+00:00
-- url     : https://prove2.me/theorems/5c0e6d8d-6481-4e36-9585-d4e106f27b52
-- title:
--   P2 M Ground Theory Heights  Heights Arith Variety mem points of generators vanish 912fad86b1ee: P2 M Ground Theory Heights  Heights Arith Variety mem points of generators vanish 912fad86b1ee
-- statement:
--   The P2 M Ground Theory Heights  Heights Arith Variety mem points of generators vanish 912fad86b1ee construction uses the P2 M Ground Theory Heights  Heights Arith Variety mem points of generators vanish 912fad86b1ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MemPointsOfGeneratorsVanish.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MemPointsOfGeneratorsVanish.lean#L36-L46

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_MemPointsOfGeneratorsVanish
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
open scoped ContDiff
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_of_generators_vanish_912fad86b1ee (P : ArithVariety n) {r : ℕ}
    {G : Fin r → MvPolynomial (Coord n) ℤ} {δ : Fin r → ι → ℕ} (hG : P.IsHomogGenerators G δ)
    {z : Cone n ℂ} (hz : BlockNonzero z) (h0 : ∀ i, evalCone z (G i) = 0) : z ∈ P.points ℂ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ArithVariety».«mem_points_of_generators_vanish» := P2M_GroundTheory_Heights__Heights_ArithVariety_mem_points_of_generators_vanish_912fad86b1ee
