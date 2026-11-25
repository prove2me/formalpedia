-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_incIdeal_le_ker_a605ce671589
-- name    : P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_incIdeal_le_ker_a605ce671589
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:53.451656+00:00
-- url     : https://prove2.me/theorems/576fb812-b37d-4a21-8c62-c9faad074603
-- title:
--   P2 M Ground Theory Heights  Heights Vertical Chart Torsion inc Ideal le ker a605ce671589: P2 M Ground Theory Heights  Heights Vertical Chart Torsion inc Ideal le ker a605ce671589
-- statement:
--   The P2 M Ground Theory Heights  Heights Vertical Chart Torsion inc Ideal le ker a605ce671589 construction uses the P2 M Ground Theory Heights  Heights Vertical Chart Torsion inc Ideal le ker a605ce671589 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartTorsion.lean#L37-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/VerticalDivisors/PChartTorsion.lean#L37-L56

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

theorem P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_incIdeal_le_ker_a605ce671589 : incIdeal P k ≤ RingHom.ker (toChart k P j) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Vertical».«ChartTorsion».«incIdeal_le_ker» := P2M_GroundTheory_Heights__Heights_Vertical_ChartTorsion_incIdeal_le_ker_a605ce671589
