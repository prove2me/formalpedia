-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_F_value_59f019138684
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_F_value_59f019138684
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:41:59.961862+00:00
-- url     : https://prove2.me/theorems/b78ad692-022a-4e34-a7be-eb217d8751bd
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover F value 59f019138684: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover F value 59f019138684
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover F value 59f019138684 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover F value 59f019138684 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L339-L355
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L339-L355

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_F_value_59f019138684 (N : ℕ) (F : S.ι → S.ν → S.κ → S.κ → MRing S.YIdx) (hF : S.IsPluckerRel N F)
    (i : S.ι) (l : S.ν) (k m : S.κ) :
    aeval (yyc S) (F i l k m) = algebraMap S.Ω S.Φ
      ((S.φ k (S.e 0) * S.φ m (S.e 1) - S.φ k (S.e 1) * S.φ m (S.e 0)) * S.δ l * S.x i ^ N) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«F_value» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_F_value_59f019138684
