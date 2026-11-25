-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_toChart_rename_90d568dd3801
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_toChart_rename_90d568dd3801
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T04:42:00.25744+00:00
-- url     : https://prove2.me/theorems/1f04e52b-d058-4bdb-bfde-a6327716bb94
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Chart Torsion to Chart rename 90d568dd3801: P2 M Ground Theory Heights  Heights Vertical Chart Torsion to Chart rename 90d568dd3801
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Chart Torsion to Chart rename 90d568dd3801 construction uses the P2 M Ground Theory Heights  Heights Vertical Chart Torsion to Chart rename 90d568dd3801 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartTorsion.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartTorsion.lean#L30-L35

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_toChart_rename_90d568dd3801 (p : MvPolynomial (Fin n) D) :
    toChart k P j (rename Sum.inl p) = C (toBase P j p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«ChartTorsion».«toChart_rename» := P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_toChart_rename_90d568dd3801
