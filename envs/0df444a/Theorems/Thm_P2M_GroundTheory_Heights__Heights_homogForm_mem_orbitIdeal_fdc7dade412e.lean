-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_homogForm_mem_orbitIdeal_fdc7dade412e
-- name    : P2M_GroundTheory_Heights__Heights_homogForm_mem_orbitIdeal_fdc7dade412e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:45.780133+00:00
-- url     : https://prove2.me/theorems/01080fe8-223b-47d5-a87b-0301f9d35005
-- title:
--   P2 M Ground Theory Heights  Heights homog Form mem orbit Ideal fdc7dade412e: P2 M Ground Theory Heights  Heights homog Form mem orbit Ideal fdc7dade412e
-- statement:
--   The P2 M Ground Theory Heights  Heights homog Form mem orbit Ideal fdc7dade412e construction uses the P2 M Ground Theory Heights  Heights homog Form mem orbit Ideal fdc7dade412e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegree.lean#L45-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitDegree.lean#L45-L69

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

theorem P2M_GroundTheory_Heights__Heights_homogForm_mem_orbitIdeal_fdc7dade412e [Fintype ι] [DecidableEq ι] (x : Cone n (AlgebraicClosure ℚ)) (g : Polynomial ℤ)
    (p q : Coord n) (hpq : p.1 = q.1) (hq : flatCone x q ≠ 0)
    (hg : Polynomial.aeval (flatCone x p / flatCone x q) g = 0) :
    homogForm g p q ∈ orbitIdeal x := by sorry

alias «GroundTheory».«Heights₂».«Heights».«homogForm_mem_orbitIdeal» := P2M_GroundTheory_Heights__Heights_homogForm_mem_orbitIdeal_fdc7dade412e
