-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ReadsMul_mConeMap_of_homog_9cd01bc91e23
-- name    : P2M_GroundTheory_Heights__Heights_ReadsMul_mConeMap_of_homog_9cd01bc91e23
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:15:57.90598+00:00
-- url     : https://prove2.me/theorems/8b82d99e-375c-471d-ab2b-9bdbadffcc41
-- title:
--   P2 M Ground Theory Heights  Heights Reads Mul m Cone Map of homog 9cd01bc91e23: P2 M Ground Theory Heights  Heights Reads Mul m Cone Map of homog 9cd01bc91e23
-- statement:
--   The P2 M Ground Theory Heights  Heights Reads Mul m Cone Map of homog 9cd01bc91e23 construction uses the P2 M Ground Theory Heights  Heights Reads Mul m Cone Map of homog 9cd01bc91e23 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PReadsMul.lean#L15-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/PReadsMul.lean#L15-L32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PReadsMul
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.ReadsMul
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_ReadsMul_mConeMap_of_homog_9cd01bc91e23 {Ω : Type} [Field Ω] (y : Coord n → Ω) {g : MvPolynomial (Coord n) ℤ}
    {d : ι → ℕ} (hg : IsWeightedHomogeneous (coordDeg n) g d) :
    Geo.mConeMap (ι := blockIdx n) y g = C (aeval y g) * ∏ k, (X k : MvPolynomial ι Ω) ^ d k := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ReadsMul».«mConeMap_of_homog» := P2M_GroundTheory_Heights__Heights_ReadsMul_mConeMap_of_homog_9cd01bc91e23
