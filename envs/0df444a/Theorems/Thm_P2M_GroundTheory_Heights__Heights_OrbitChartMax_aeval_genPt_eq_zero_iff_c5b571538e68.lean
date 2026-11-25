-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_genPt_eq_zero_iff_c5b571538e68
-- name    : P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_genPt_eq_zero_iff_c5b571538e68
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:20:23.715677+00:00
-- url     : https://prove2.me/theorems/b43efa24-3a09-5962-9e3b-aebf59368b82
-- title:
--   P2 M Ground Theory Heights  Heights Orbit Chart Max aeval gen Pt eq zero iff c5b571538e68: P2 M Ground Theory Heights  Heights Orbit Chart Max aeval gen Pt eq zero iff c5b571538e68
-- statement:
--   The P2 M Ground Theory Heights  Heights Orbit Chart Max aeval gen Pt eq zero iff c5b571538e68 construction uses the P2 M Ground Theory Heights  Heights Orbit Chart Max aeval gen Pt eq zero iff c5b571538e68 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L178-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartMax.lean#L178-L180

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

theorem P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_genPt_eq_zero_iff_c5b571538e68 (F : MvPolynomial (Coord n) ℤ) : aeval (genPt V) F = 0 ↔ F ∈ V := by sorry

alias «GroundTheory».«Heights₂».«Heights».«OrbitChartMax».«aeval_genPt_eq_zero_iff» := P2M_GroundTheory_Heights__Heights_OrbitChartMax_aeval_genPt_eq_zero_iff_c5b571538e68
