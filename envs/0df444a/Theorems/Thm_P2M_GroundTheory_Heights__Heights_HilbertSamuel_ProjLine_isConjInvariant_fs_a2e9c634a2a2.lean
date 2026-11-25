-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isConjInvariant_fs_a2e9c634a2a2
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isConjInvariant_fs_a2e9c634a2a2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:19:49.52514+00:00
-- url     : https://prove2.me/theorems/7c11450a-6bc4-4ffc-8d5c-c7d14248640e
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Conj Invariant fs a2e9c634a2a2: P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Conj Invariant fs a2e9c634a2a2
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Conj Invariant fs a2e9c634a2a2 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Conj Invariant fs a2e9c634a2a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L350-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L350-L354

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isConjInvariant_fs_a2e9c634a2a2 : IsConjInvariant (fsMetric J) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ProjLine».«isConjInvariant_fs» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isConjInvariant_fs_a2e9c634a2a2
