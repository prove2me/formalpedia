-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_eulerDirs_finrank_2122c098d3ee
-- name    : P2M_GroundTheory_Heights__Heights_Inter_eulerDirs_finrank_2122c098d3ee
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:53.793022+00:00
-- url     : https://prove2.me/theorems/0e8fc789-11ae-4260-af32-bb7bf20fdfa4
-- title:
--   P2 M Ground Theory Heights  Heights Inter euler Dirs finrank 2122c098d3ee: P2 M Ground Theory Heights  Heights Inter euler Dirs finrank 2122c098d3ee
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter euler Dirs finrank 2122c098d3ee construction uses the P2 M Ground Theory Heights  Heights Inter euler Dirs finrank 2122c098d3ee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFIntZero.lean#L28-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PPFIntZero.lean#L28-L59

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsPFIntZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMapAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeviOfRealSmulRight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_TableDegreeThreeBase
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFIntZeroMixed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFIntZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_eulerDirs_finrank_2122c098d3ee (hR : pointFormRank_holds.Statement) {Q : Ideal (MRing ι)} {d n : ℕ} (hQ : IsArithVar Q d)
    {F : (Fin n → ℂ) → (Σ k, ι k) → ℂ} {y : Fin n → ℂ} (hF : AnalyticAt ℂ F y)
    (hFQ : ∀ᶠ y' in 𝓝 y, F y' ∈ mcPts Q) : n < Module.finrank ℂ (eulerDirs F y) + d := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«eulerDirs_finrank» := P2M_GroundTheory_Heights__Heights_Inter_eulerDirs_finrank_2122c098d3ee
