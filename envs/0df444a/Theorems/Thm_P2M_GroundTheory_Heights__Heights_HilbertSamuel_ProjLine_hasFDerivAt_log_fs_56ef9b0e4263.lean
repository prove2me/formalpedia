-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_hasFDerivAt_log_fs_56ef9b0e4263
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_hasFDerivAt_log_fs_56ef9b0e4263
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:21:42.218802+00:00
-- url     : https://prove2.me/theorems/b62ebce3-a6cc-58c5-8290-853081ccc019
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line has FDeriv At log fs 56ef9b0e4263: P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line has FDeriv At log fs 56ef9b0e4263
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line has FDeriv At log fs 56ef9b0e4263 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line has FDeriv At log fs 56ef9b0e4263 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L276-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L276-L283

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_hasFDerivAt_log_fs_56ef9b0e4263 {y : J → ℂ} (hy : y ≠ 0) :
    HasFDerivAt (fun z => Real.log ((fsMetric J).ρ z)) ((normSqE y)⁻¹ • reInner y) y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ProjLine».«hasFDerivAt_log_fs» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_hasFDerivAt_log_fs_56ef9b0e4263
