-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_standard_coord_integral_2758d376c410
-- name    : P2M_GroundTheory_Heights__Heights_standard_coord_integral_2758d376c410
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T04:56:45.97642+00:00
-- url     : https://prove2.me/theorems/d0a89007-c434-57f7-bc69-be33be271ab6
-- title:
--   P2 M Ground Theory Heights  Heights standard coord integral 2758d376c410: P2 M Ground Theory Heights  Heights standard coord integral 2758d376c410
-- statement:
--   The P2 M Ground Theory Heights  Heights standard coord integral 2758d376c410 construction uses the P2 M Ground Theory Heights  Heights standard coord integral 2758d376c410 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockStandard.lean#L13-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/POneBlockStandard.lean#L13-L30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_POneBlockStandard
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
open MvPolynomial NumberField Matrix
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem P2M_GroundTheory_Heights__Heights_standard_coord_integral_2758d376c410 {m : ℕ} {v : Fin m → K}
    (hv : v ∈ (HermLattice.standard K m).lattice) (i : Fin m) :
    ∃ b : 𝓞 K, v i = algebraMap (𝓞 K) K b := by sorry

alias «GroundTheory».«Heights₂».«Heights».«standard_coord_integral» := P2M_GroundTheory_Heights__Heights_standard_coord_integral_2758d376c410
