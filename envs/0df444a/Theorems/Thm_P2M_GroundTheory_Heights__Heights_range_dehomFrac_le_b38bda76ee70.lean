-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_range_dehomFrac_le_b38bda76ee70
-- name    : P2M_GroundTheory_Heights__Heights_range_dehomFrac_le_b38bda76ee70
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T04:51:40.512859+00:00
-- url     : https://prove2.me/theorems/4a0b4711-fdeb-4cf4-a1b4-620baf60b448
-- title:
--   P2 M Ground Theory Heights  Heights range dehom Frac le b38bda76ee70: P2 M Ground Theory Heights  Heights range dehom Frac le b38bda76ee70
-- statement:
--   The P2 M Ground Theory Heights  Heights range dehom Frac le b38bda76ee70 construction uses the P2 M Ground Theory Heights  Heights range dehom Frac le b38bda76ee70 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartDehom.lean#L107-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/POrbitChartDehom.lean#L107-L131

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartDehom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCenterDivSuppLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSupSpanMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartDehom
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
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
variable (V : Ideal (MvPolynomial (Coord n) ℤ)) [V.IsPrime]
variable {V}
omit [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_range_dehomFrac_le_b38bda76ee70 {c c' : (k : ι) → Fin (n k + 1)}
    (hc : ∀ k, (X ⟨k, c k⟩ : MvPolynomial (Coord n) ℤ) ∉ V)
    (hc' : ∀ k, (X ⟨k, c' k⟩ : MvPolynomial (Coord n) ℤ) ∉ V)
    (hF : IsField (dehomFrac V c).range) : (dehomFrac V c').range ≤ (dehomFrac V c).range := by sorry

alias «GroundTheory».«Heights₂».«Heights».«range_dehomFrac_le» := P2M_GroundTheory_Heights__Heights_range_dehomFrac_le_b38bda76ee70
