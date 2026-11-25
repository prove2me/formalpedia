-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_val_aeval_ratioVec_1b40d5b88b4d
-- name    : P2M_GroundTheory_Heights__Heights_val_aeval_ratioVec_1b40d5b88b4d
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:48:09.007205+00:00
-- url     : https://prove2.me/theorems/5624447c-4fe5-5f83-9d9e-232db9763201
-- title:
--   P2 M Ground Theory Heights  Heights val aeval ratio Vec 1b40d5b88b4d: P2 M Ground Theory Heights  Heights val aeval ratio Vec 1b40d5b88b4d
-- statement:
--   The P2 M Ground Theory Heights  Heights val aeval ratio Vec 1b40d5b88b4d construction uses the P2 M Ground Theory Heights  Heights val aeval ratio Vec 1b40d5b88b4d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatio.lean#L17-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegreeRatio.lean#L17-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatioLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegreeRatio
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
variable {ι : Type} {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_val_aeval_ratioVec_1b40d5b88b4d (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (f : MvPolynomial (Coord n) ℚ) :
    ((aeval (ratioVec x c) f : ratioField x) : AlgebraicClosure ℚ) =
      aeval (fun p : Coord n ↦ x p.1 p.2 / x p.1 (c p.1)) f := by sorry

alias «GroundTheory».«Heights₂».«Heights».«val_aeval_ratioVec» := P2M_GroundTheory_Heights__Heights_val_aeval_ratioVec_1b40d5b88b4d
