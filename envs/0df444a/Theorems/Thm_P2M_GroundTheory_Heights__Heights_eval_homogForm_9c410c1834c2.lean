-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_eval_homogForm_9c410c1834c2
-- name    : P2M_GroundTheory_Heights__Heights_eval_homogForm_9c410c1834c2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:33:59.153541+00:00
-- url     : https://prove2.me/theorems/1af0c930-5b6b-4835-9cb6-974622cb7c01
-- title:
--   P2 M Ground Theory Heights  Heights eval homog Form 9c410c1834c2: P2 M Ground Theory Heights  Heights eval homog Form 9c410c1834c2
-- statement:
--   The P2 M Ground Theory Heights  Heights eval homog Form 9c410c1834c2 construction uses the P2 M Ground Theory Heights  Heights eval homog Form 9c410c1834c2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegree.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegree.lean#L16-L19

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitDegree
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

theorem P2M_GroundTheory_Heights__Heights_eval_homogForm_9c410c1834c2 (g : Polynomial ℤ) (p q : Coord n) (z : Coord n → ℂ) :
    eval z (map (Int.castRingHom ℂ) (homogForm g p q)) =
      ∑ j ∈ Finset.range (g.natDegree + 1), (g.coeff j : ℂ) * z p ^ j * z q ^ (g.natDegree - j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«eval_homogForm» := P2M_GroundTheory_Heights__Heights_eval_homogForm_9c410c1834c2
