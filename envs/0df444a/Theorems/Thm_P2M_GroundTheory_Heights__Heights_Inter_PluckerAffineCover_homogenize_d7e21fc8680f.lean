-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homogenize_d7e21fc8680f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homogenize_d7e21fc8680f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:25:09.408921+00:00
-- url     : https://prove2.me/theorems/f0ea740a-91df-4225-951d-12ec3dd866fb
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover homogenize d7e21fc8680f: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover homogenize d7e21fc8680f
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover homogenize d7e21fc8680f construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover homogenize d7e21fc8680f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L252-L284
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L252-L284

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homogenize_d7e21fc8680f (i : S.ι) (hx : S.x i ≠ 0) {a : S.Ω} (ha : a ∈ chartRing ℤ S.x i) :
    ∃ (d : ℕ) (P : MRing S.YIdx), IsWeightedHomogeneous (wt S) P (Pi.single .base d) ∧
      aeval (yyc S) P = algebraMap S.Ω S.Φ (a * S.x i ^ d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«homogenize» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_homogenize_d7e21fc8680f
