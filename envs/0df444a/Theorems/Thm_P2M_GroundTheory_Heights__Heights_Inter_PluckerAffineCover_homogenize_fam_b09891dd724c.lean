-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homogenize_fam_b09891dd724c
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homogenize_fam_b09891dd724c
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:30:25.055411+00:00
-- url     : https://prove2.me/theorems/af542734-f7de-5e4d-b9ad-5aaaf5f03e67
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover homogenize fam b09891dd724c: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover homogenize fam b09891dd724c
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover homogenize fam b09891dd724c construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover homogenize fam b09891dd724c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L286-L300
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L286-L300

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homogenize_fam_b09891dd724c (i : S.ι) (hx : S.x i ≠ 0) {α : Type} [Fintype α] (a : α → S.Ω)
    (ha : ∀ t, a t ∈ chartRing ℤ S.x i) :
    ∃ (d : ℕ) (P : α → MRing S.YIdx), ∀ t, IsWeightedHomogeneous (wt S) (P t) (Pi.single .base d) ∧
      aeval (yyc S) (P t) = algebraMap S.Ω S.Φ (a t * S.x i ^ d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«homogenize_fam» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homogenize_fam_b09891dd724c
