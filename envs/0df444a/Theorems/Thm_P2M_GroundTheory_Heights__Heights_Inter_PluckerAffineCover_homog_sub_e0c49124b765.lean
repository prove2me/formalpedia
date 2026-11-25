-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homog_sub_e0c49124b765
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homog_sub_e0c49124b765
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:25:15.467264+00:00
-- url     : https://prove2.me/theorems/eecfb4cf-b34a-4026-9be2-af74ab81b6d3
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover homog sub e0c49124b765: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover homog sub e0c49124b765
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover homog sub e0c49124b765 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover homog sub e0c49124b765 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L248-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L248-L250

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerCover
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PPFFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerCover
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerAffineCover
variable {D : ℕ} (S : ProjectiveLineBundle D)

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homog_sub_e0c49124b765 {p q : MRing S.YIdx} {m : T.YBlk → ℕ} (hp : IsWeightedHomogeneous (wt S) p m)
    (hq : IsWeightedHomogeneous (wt S) q m) : IsWeightedHomogeneous (wt S) (p - q) m := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«homog_sub» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homog_sub_e0c49124b765
