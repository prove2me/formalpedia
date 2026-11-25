-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_good_of_e28dc548cf6c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_good_of_e28dc548cf6c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:57.726643+00:00
-- url     : https://prove2.me/theorems/aff4d0ec-e6f8-41cd-8220-45e0cb253c23
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover good of e28dc548cf6c: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover good of e28dc548cf6c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover good of e28dc548cf6c construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover good of e28dc548cf6c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L360-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L360-L363

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_good_of_e28dc548cf6c {r : MRing S.YIdx} {d : ℕ} (hr : IsWeightedHomogeneous (wt S) r (Pi.single .base d))
    (h0 : aeval (yyc S) r = 0) : Good S r := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«good_of» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_good_of_e28dc548cf6c
