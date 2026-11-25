-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_comp_perm_4fe32ebbcec2
-- name    : P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_comp_perm_4fe32ebbcec2
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:23:56.109484+00:00
-- url     : https://prove2.me/theorems/5bf765cb-bfb6-48ef-9aed-12695d24da66
-- title:
--   P2 M Ground Theory Heights  Heights Inter mixed Disc comp perm 4fe32ebbcec2: P2 M Ground Theory Heights  Heights Inter mixed Disc comp perm 4fe32ebbcec2
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter mixed Disc comp perm 4fe32ebbcec2 construction uses the P2 M Ground Theory Heights  Heights Inter mixed Disc comp perm 4fe32ebbcec2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L16-L22

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {D : ℕ}

theorem P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_comp_perm_4fe32ebbcec2 (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (σ : Equiv.Perm (Fin D)) :
    mixedDisc (A ∘ σ) = mixedDisc A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«mixedDisc_comp_perm» := P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_comp_perm_4fe32ebbcec2
