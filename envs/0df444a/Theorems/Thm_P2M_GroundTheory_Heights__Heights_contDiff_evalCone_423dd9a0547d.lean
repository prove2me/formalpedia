-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_evalCone_423dd9a0547d
-- name    : P2M_GroundTheory_Heights__Heights_contDiff_evalCone_423dd9a0547d
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:45:57.11506+00:00
-- url     : https://prove2.me/theorems/22c690f8-e379-4a6d-a203-5ab1c34e7610
-- title:
--   P2 M Ground Theory Heights  Heights cont Diff eval Cone 423dd9a0547d: P2 M Ground Theory Heights  Heights cont Diff eval Cone 423dd9a0547d
-- statement:
--   The P2 M Ground Theory Heights  Heights cont Diff eval Cone 423dd9a0547d construction uses the P2 M Ground Theory Heights  Heights cont Diff eval Cone 423dd9a0547d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MemPointsOfGeneratorsVanish.lean#L16-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/MemPointsOfGeneratorsVanish.lean#L16-L23

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
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_contDiff_evalCone_423dd9a0547d (f : MvPolynomial (Coord n) ℤ) :
    ContDiff ℝ ∞ (fun z : Cone n ℂ ↦ evalCone z f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«contDiff_evalCone» := P2M_GroundTheory_Heights__Heights_contDiff_evalCone_423dd9a0547d
