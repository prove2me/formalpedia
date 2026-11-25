-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_mass_b3b259448c07
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_mass_b3b259448c07
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:34:54.769852+00:00
-- url     : https://prove2.me/theorems/fdd9fe58-5575-5ed2-9888-f7451eac0cf7
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B open Atlas mass b3b259448c07: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B open Atlas mass b3b259
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B open Atlas mass b3b259448c07 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B open Atlas mass b3b259448c07 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OpenAtlasSymmEventuallyEq.lean#L55-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OpenAtlasSymmEventuallyEq.lean#L55-L85

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_LeviFormGbPotOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_OpenAtlasSymmEventuallyEq
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_mass_b3b259448c07 {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω)
    (Q : LocPot Ω) (F : (Fin D → ℂ) → ℝ) (hQ : ∀ x z, Q.φ x z = F z / 2) :
    maMeasure (openAtlas Ω hΩ) (fun _ => Q) Set.univ =
      ∫⁻ z in (Ω : Set (Fin D → ℂ)), ENNReal.ofReal (topDens F z) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«FourB».«openAtlas_mass» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_mass_b3b259448c07
