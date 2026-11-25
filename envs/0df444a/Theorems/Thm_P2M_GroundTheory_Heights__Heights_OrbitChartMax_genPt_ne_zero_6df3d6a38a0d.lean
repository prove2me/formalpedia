-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_genPt_ne_zero_6df3d6a38a0d
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMax_genPt_ne_zero_6df3d6a38a0d
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:42.401651+00:00
-- url     : https://prove2.me/theorems/80129e43-872c-42a5-bb68-aa84d051c347
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Max gen Pt ne zero 6df3d6a38a0d: P2 M Ground Theory Heights  Heights Orbit Chart Max gen Pt ne zero 6df3d6a38a0d
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Max gen Pt ne zero 6df3d6a38a0d construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Max gen Pt ne zero 6df3d6a38a0d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L184-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L184-L186

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax
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
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMax
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (V : Ideal (MvPolynomial (Coord n) ℤ)) [V.IsPrime]
omit [Fintype ι] [DecidableEq ι] [V.IsPrime]

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMax_genPt_ne_zero_6df3d6a38a0d {p : Coord n} (hp : (X p : MvPolynomial (Coord n) ℤ) ∉ V) : genPt V p ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMax».«genPt_ne_zero» := P2M_GroundTheory_Heights__Heights_OrbitChartMax_genPt_ne_zero_6df3d6a38a0d
