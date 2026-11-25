-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_isNumPolyLT_comp_26fb9bdb9ce0
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_isNumPolyLT_comp_26fb9bdb9ce0
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:57:40.854194+00:00
-- url     : https://prove2.me/theorems/1cb76524-f409-45e1-9e22-087d7ea8baf6
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly is Num Poly LT comp 26fb9bdb9ce0: P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly is Num Poly LT comp 26fb9bdb9ce0
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly is Num Poly LT comp 26fb9bdb9ce0 construction uses the P2 M Ground Theory Heights  Heights Kleiman Snapper Diff Poly is Num Poly LT comp 26fb9bdb9ce0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDiffPoly.lean#L57-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PSnapperDiffPoly.lean#L57-L69

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SnapperDiffPolySt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPolyOfDiffs
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSnapperDiffPoly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Kleiman.SnapperDiffPoly

theorem P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_isNumPolyLT_comp_26fb9bdb9ce0 {t D : ℕ} {F G : (Fin t → ℕ) → ℤ → ℚ} (σ : Fin (t + 1) → MvPolynomial (Fin (t + 1)) ℚ)
    (hσ : ∀ i, (σ i).totalDegree ≤ 1) (a : (Fin t → ℕ) → ℤ → (Fin t → ℕ)) (b : (Fin t → ℕ) → ℤ → ℤ)
    (hab : ∀ n c, (fun i => eval (numPt n c) (σ i)) = numPt (a n c) (b n c))
    (hG : ∀ n c, G n c = F (a n c) (b n c)) (hF : IsNumPolyLT t D F) : IsNumPolyLT t D G := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«SnapperDiffPoly».«isNumPolyLT_comp» := P2M_GroundTheory_Heights__Heights_Kleiman_SnapperDiffPoly_isNumPolyLT_comp_26fb9bdb9ce0
