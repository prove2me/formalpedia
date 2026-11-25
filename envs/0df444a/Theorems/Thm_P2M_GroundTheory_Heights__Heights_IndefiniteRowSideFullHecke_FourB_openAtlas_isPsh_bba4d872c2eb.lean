-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_isPsh_bba4d872c2eb
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_isPsh_bba4d872c2eb
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:35:56.118464+00:00
-- url     : https://prove2.me/theorems/96f846c6-bddd-4481-84ec-7a1a90738b12
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B open Atlas is Psh bba4d872c2eb: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B open Atlas is Psh bb
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B open Atlas is Psh bba4d872c2eb construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Four B open Atlas is Psh bba4d872c2eb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OpenAtlasSymmEventuallyEq.lean#L100-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LocalDensities/OpenAtlasSymmEventuallyEq.lean#L100-L121

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_isPsh_bba4d872c2eb {D : ℕ} (Ω : TopologicalSpace.Opens (Fin D → ℂ)) (hΩ : Nonempty Ω)
    (Q : LocPot Ω) (F : (Fin D → ℂ) → ℝ) (hQ : ∀ x z, Q.φ x z = F z / 2)
    (hF : ContDiffOn ℝ ∞ F Ω) (hL : ∀ z ∈ (Ω : Set (Fin D → ℂ)), ∀ w, 0 ≤ leviForm F z w) :
    IsPsh (openAtlas Ω hΩ) Q := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«FourB».«openAtlas_isPsh» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FourB_openAtlas_isPsh_bba4d872c2eb
