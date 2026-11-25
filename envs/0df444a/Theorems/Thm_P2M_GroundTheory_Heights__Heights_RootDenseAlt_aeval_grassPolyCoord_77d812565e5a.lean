-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_grassPolyCoord_77d812565e5a
-- name    : P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_grassPolyCoord_77d812565e5a
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:37:04.524324+00:00
-- url     : https://prove2.me/theorems/f030046d-1d03-4f9d-a7aa-02c647f578a3
-- title:
--   P2 M Ground Theory Heights  Heights Root Dense Alt aeval grass Poly Coord 77d812565e5a: P2 M Ground Theory Heights  Heights Root Dense Alt aeval grass Poly Coord 77d812565e5a
-- statement:
--   The P2 M Ground Theory Heights  Heights Root Dense Alt aeval grass Poly Coord 77d812565e5a construction uses the P2 M Ground Theory Heights  Heights Root Dense Alt aeval grass Poly Coord 77d812565e5a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootDense.lean#L13-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PRootDense.lean#L13-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PRootDense
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.RootDenseAlt

theorem P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_grassPolyCoord_77d812565e5a {f j m : ℕ} (x : Fin f × Fin j × Fin m → ℂ)
    (p : Σ _ : Fin f, PlIdx j m) :
    aeval x (grassPolyCoord f j m p) = rootCoord (fun τ a b => x (τ, a, b)) p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«RootDenseAlt».«aeval_grassPolyCoord» := P2M_GroundTheory_Heights__Heights_RootDenseAlt_aeval_grassPolyCoord_77d812565e5a
