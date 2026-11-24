-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_orbitIdeal_iff_of_isMultiHomog_796bb3d2097e
-- name    : P2M_GroundTheory_Heights__Heights_mem_orbitIdeal_iff_of_isMultiHomog_796bb3d2097e
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:16.909714+00:00
-- url     : https://prove2.me/theorems/de2886ce-8200-444d-9fed-8eb5295cd234
-- title:
--   P2 M Ground Theory Heights  Heights mem orbit Ideal iff of is Multi Homog 796bb3d2097e: P2 M Ground Theory Heights  Heights mem orbit Ideal iff of is Multi Homog 796bb3d2097e
-- statement:
--   The P2 M Ground Theory Heights  Heights mem orbit Ideal iff of is Multi Homog 796bb3d2097e construction uses the P2 M Ground Theory Heights  Heights mem orbit Ideal iff of is Multi Homog 796bb3d2097e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterDivSuppLemmas.lean#L58-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitCenterDivSuppLemmas.lean#L58-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenter
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PHeightRecR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCenterMemIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterDivSuppLemmas
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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_mem_orbitIdeal_iff_of_isMultiHomog_796bb3d2097e (x : Cone n (AlgebraicClosure ℚ))
    (F : MvPolynomial (Coord n) ℤ) (a : ι → ℕ) (hF : Geo.IsMultiHomog (ι := blockIdx n) F a) :
    F ∈ orbitIdeal x ↔ evalCone (coordVec x) F = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«mem_orbitIdeal_iff_of_isMultiHomog» := P2M_GroundTheory_Heights__Heights_mem_orbitIdeal_iff_of_isMultiHomog_796bb3d2097e
