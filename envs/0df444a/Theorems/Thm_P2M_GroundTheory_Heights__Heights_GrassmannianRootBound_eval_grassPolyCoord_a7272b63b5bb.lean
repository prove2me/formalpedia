-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_GrassmannianRootBound_eval_grassPolyCoord_a7272b63b5bb
-- name    : P2M_GroundTheory_Heights__Heights_GrassmannianRootBound_eval_grassPolyCoord_a7272b63b5bb
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:18:01.038881+00:00
-- url     : https://prove2.me/theorems/877618b2-83c2-40b5-971f-343fe62e23bf
-- title:
--   P2 M Ground Theory Heights  Heights Grassmannian Root Bound eval grass Poly Coord a7272b63b5bb: P2 M Ground Theory Heights  Heights Grassmannian Root Bound eval grass Poly Coord a7272b63b5bb
-- statement:
--   The P2 M Ground Theory Heights  Heights Grassmannian Root Bound eval grass Poly Coord a7272b63b5bb construction uses the P2 M Ground Theory Heights  Heights Grassmannian Root Bound eval grass Poly Coord a7272b63b5bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassLeRoot.lean#L27-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/PGrassLeRoot.lean#L27-L40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrassHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PGrassLeRoot
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
open GroundTheory.Heights₂.Heights.GrassmannianRootBound
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_GrassmannianRootBound_eval_grassPolyCoord_a7272b63b5bb {f j m : ℕ} (ζ : Fin f → Matrix (Fin j) (Fin m) ℂ)
    (p : Σ _ : Fin f, PlIdx j m) :
    aeval (fun q : Fin f × Fin j × Fin m => ζ q.1 q.2.1 q.2.2) (grassPolyCoord f j m p) =
      rootCoord ζ p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«GrassmannianRootBound».«eval_grassPolyCoord» := P2M_GroundTheory_Heights__Heights_GrassmannianRootBound_eval_grassPolyCoord_a7272b63b5bb
