-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isConjInvariantH_fs_e9afde28417e
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isConjInvariantH_fs_e9afde28417e
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:15:43.475033+00:00
-- url     : https://prove2.me/theorems/f49239db-f0a2-4343-8edb-c6cb9892a496
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Conj Invariant H fs e9afde28417e: P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Conj Invariant H fs e9afde28417e
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Conj Invariant H fs e9afde28417e construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Proj Line is Conj Invariant H fs e9afde28417e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L370-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/ArithModel.lean#L370-L371

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isConjInvariantH_fs_e9afde28417e (κ : Type) [Fintype κ] : IsConjInvariantH (HermLine.ofCone (fsMetric (Ix κ))) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«ProjLine».«isConjInvariantH_fs» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_isConjInvariantH_fs_e9afde28417e
