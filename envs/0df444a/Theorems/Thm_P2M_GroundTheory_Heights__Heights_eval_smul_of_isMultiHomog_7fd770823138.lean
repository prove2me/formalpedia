-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_smul_of_isMultiHomog_7fd770823138
-- name    : P2M_GroundTheory_Heights__Heights_eval_smul_of_isMultiHomog_7fd770823138
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:46:36.53768+00:00
-- url     : https://prove2.me/theorems/f1987fe9-0993-43a9-8c36-607dc1644f64
-- title:
--   P2 M Ground Theory Heights  Heights eval smul of is Multi Homog 7fd770823138: P2 M Ground Theory Heights  Heights eval smul of is Multi Homog 7fd770823138
-- statement:
--   The P2 M Ground Theory Heights  Heights eval smul of is Multi Homog 7fd770823138 construction uses the P2 M Ground Theory Heights  Heights eval smul of is Multi Homog 7fd770823138 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitArchSum.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitArchSum.lean#L13-L28

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitArchSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitConjSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitArchSum
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
variable {ι : Type} [Fintype ι] {n : ι → ℕ}

theorem P2M_GroundTheory_Heights__Heights_eval_smul_of_isMultiHomog_7fd770823138 (s : MvPolynomial (Coord n) ℤ) (a : ι → ℕ)
    (hs : Geo.IsMultiHomog (ι := blockIdx n) s a) (c : ι → ℂ) (z : Coord n → ℂ) :
    eval (fun p ↦ c p.1 * z p) (map (Int.castRingHom ℂ) s) =
      (∏ k, c k ^ a k) * eval z (map (Int.castRingHom ℂ) s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eval_smul_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_eval_smul_of_isMultiHomog_7fd770823138
