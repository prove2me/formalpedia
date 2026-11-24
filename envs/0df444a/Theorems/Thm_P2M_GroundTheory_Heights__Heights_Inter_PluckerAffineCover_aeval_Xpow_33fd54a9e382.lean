-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_aeval_Xpow_33fd54a9e382
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_aeval_Xpow_33fd54a9e382
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:52.66308+00:00
-- url     : https://prove2.me/theorems/3f569f38-e81c-4a39-8426-dd5a0a9ecc35
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover aeval Xpow 33fd54a9e382: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover aeval Xpow 33fd54a9e382
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover aeval Xpow 33fd54a9e382 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover aeval Xpow 33fd54a9e382 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L232-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L232-L234

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_aeval_Xpow_33fd54a9e382 (i : S.ι) (d : ℕ) :
    aeval (yyc S) (X ⟨.base, i⟩ ^ d : MRing S.YIdx) = algebraMap S.Ω S.Φ (S.x i ^ d) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«aeval_Xpow» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_aeval_Xpow_33fd54a9e382
