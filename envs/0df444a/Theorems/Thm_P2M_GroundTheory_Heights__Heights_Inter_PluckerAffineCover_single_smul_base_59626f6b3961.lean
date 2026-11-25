-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_single_smul_base_59626f6b3961
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_single_smul_base_59626f6b3961
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:22.5785+00:00
-- url     : https://prove2.me/theorems/c277daa5-0157-4b74-890b-32bebf2a6537
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover single smul base 59626f6b3961: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover single smul base 59626f6b3961
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover single smul base 59626f6b3961 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover single smul base 59626f6b3961 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L243-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L243-L246

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_single_smul_base_59626f6b3961 (n d : ℕ) : n • (Pi.single .base d : T.YBlk → ℕ) = Pi.single .base (n * d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«single_smul_base» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_single_smul_base_59626f6b3961
