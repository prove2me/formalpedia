-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_multiConeMap_rename0_a76163a15ff8
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_multiConeMap_rename0_a76163a15ff8
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:37:40.944154+00:00
-- url     : https://prove2.me/theorems/f9f8370b-9d17-417d-9464-37b800d31916
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover multi Cone Map rename0 a76163a15ff8: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover multi Cone Map rename0 a76163a15ff8
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover multi Cone Map rename0 a76163a15ff8 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover multi Cone Map rename0 a76163a15ff8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L317-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L317-L326

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_multiConeMap_rename0_a76163a15ff8 {Φ : Type} [Field Φ] (c : (Σ k, S.WIdx k) → Φ) (s : MRing S.YIdx) :
    T.multiConeMap c (rename (T.yyEmb 0) s) = rename blk0 (T.multiConeMap (c ∘ T.yyEmb 0) s) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«multiConeMap_rename0» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_multiConeMap_rename0_a76163a15ff8
