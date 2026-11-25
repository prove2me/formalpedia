-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_inclChart_symm_08c35d356223
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_inclChart_symm_08c35d356223
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:35:17.290888+00:00
-- url     : https://prove2.me/theorems/f3b794e0-fa5d-4ed6-a318-05c80eabf142
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B MACompact incl Chart symm 08c35d356223: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B MACompact in
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B MACompact incl Chart symm 08c35d356223 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B MACompact incl Chart symm 08c35d356223 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OneChartAtlasIndexEq.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OneChartAtlasIndexEq.lean#L48-L51

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OneChartAtlasIndexEq
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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
open MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB.MACompact
variable {D : ℕ} {Ω : Set (Fin D → ℂ)}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_inclChart_symm_08c35d356223 (hΩ : IsOpen Ω) [Nonempty Ω] (y : Fin D → ℂ) (hy : y ∈ Ω) :
    (((inclChart hΩ).symm y : Ω) : Fin D → ℂ) = y := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«FourB».«MACompact».«inclChart_symm» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_MACompact_inclChart_symm_08c35d356223
