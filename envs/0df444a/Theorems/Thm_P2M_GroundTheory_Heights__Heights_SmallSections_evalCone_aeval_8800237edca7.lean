-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_SmallSections_evalCone_aeval_8800237edca7
-- name    : P2M_GroundTheory_Heights__Heights_SmallSections_evalCone_aeval_8800237edca7
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T05:14:09.614808+00:00
-- url     : https://prove2.me/theorems/fd7b3c8f-cd89-4843-b115-5a1ddd08088a
-- title:
--   P2 M Ground Theory Heights  Heights Small Sections eval Cone aeval 8800237edca7: P2 M Ground Theory Heights  Heights Small Sections eval Cone aeval 8800237edca7
-- statement:
--   The P2 M Ground Theory Heights  Heights Small Sections eval Cone aeval 8800237edca7 construction uses the P2 M Ground Theory Heights  Heights Small Sections eval Cone aeval 8800237edca7 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L56-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/WeightedHomogeneous/IsWeightedHomogeneousAeval.lean#L56-L62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_IsWeightedHomogeneousAeval
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
noncomputable section
open GroundTheory.Heights₂.Heights.SmallSections
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_SmallSections_evalCone_aeval_8800237edca7 {σ : Type*} (z : Cone n ℂ) (g : σ → MvPolynomial (Coord n) ℤ)
    (F : MvPolynomial σ ℤ) :
    evalCone z (aeval g F) = eval₂ (Int.castRingHom ℂ) (fun j ↦ evalCone z (g j)) F := by sorry

alias «GroundTheory».«Heights₂».«Heights».«SmallSections».«evalCone_aeval» := P2M_GroundTheory_Heights__Heights_SmallSections_evalCone_aeval_8800237edca7
