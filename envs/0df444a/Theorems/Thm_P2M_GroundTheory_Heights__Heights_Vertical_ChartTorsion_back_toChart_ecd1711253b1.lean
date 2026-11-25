-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_back_toChart_ecd1711253b1
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_back_toChart_ecd1711253b1
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T04:42:09.851158+00:00
-- url     : https://prove2.me/theorems/3320ee9d-7c13-4d89-972f-841e653150d0
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Chart Torsion back to Chart ecd1711253b1: P2 M Ground Theory Heights  Heights Vertical Chart Torsion back to Chart ecd1711253b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Chart Torsion back to Chart ecd1711253b1 construction uses the P2 M Ground Theory Heights  Heights Vertical Chart Torsion back to Chart ecd1711253b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartTorsion.lean#L88-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartTorsion.lean#L88-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.ChartTorsion
variable {D : Type} [CommRing D] {n : ℕ} (k : ℕ) (P : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)

theorem P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_back_toChart_ecd1711253b1 (g : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D) :
    back k P j (toChart k P j g) = toLoc k P j g := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«ChartTorsion».«back_toChart» := P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_back_toChart_ecd1711253b1
