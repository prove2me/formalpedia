-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_leviForm_log_fs_nonneg_4c974b17d733
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_leviForm_log_fs_nonneg_4c974b17d733
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:06:26.908507+00:00
-- url     : https://prove2.me/theorems/9e411c46-af4f-4539-a96a-70b1302a90ef
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line levi Form log fs nonneg 4c974b17d733: P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line levi Form log fs nonneg 4c974b17d733
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line levi Form log fs nonneg 4c974b17d733 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line levi Form log fs nonneg 4c974b17d733 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L285-L338
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L285-L338

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsSmoothPts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.HilbertSamuel.ProjLine
open scoped Topology
variable {J : Type} [Fintype J]

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_leviForm_log_fs_nonneg_4c974b17d733 {z : J → ℂ} (hz : z ≠ 0) (w : J → ℂ) :
    0 ≤ leviForm (fun z => Real.log ((fsMetric J).ρ z)) z w := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ProjLine».«leviForm_log_fs_nonneg» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_leviForm_log_fs_nonneg_4c974b17d733
