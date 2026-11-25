-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_aeval_of_mem_ker_c4e20c757a43
-- name    : P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_aeval_of_mem_ker_c4e20c757a43
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:24:56.200802+00:00
-- url     : https://prove2.me/theorems/599af100-3b40-4210-b74b-f090224c7622
-- title:
--   P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover aeval of mem ker c4e20c757a43: P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover aeval of mem ker c4e20c757a43
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover aeval of mem ker c4e20c757a43 construction uses the P2 M Ground Theory Heights  Heights Inter Plucker Affine Cover aeval of mem ker c4e20c757a43 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L302-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ElementarySymmetric/PPluckerCover.lean#L302-L310

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

theorem P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_aeval_of_mem_ker_c4e20c757a43 {K : Type} {ι : K → Type} {Φ : Type} [Field Φ] (c : (Σ k, ι k) → Φ) {p : MRing ι}
    (hp : p ∈ RingHom.ker (T.multiConeMap c)) : aeval c p = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«PluckerAffineCover».«aeval_of_mem_ker» := P2M_GroundTheory_Heights__Heights_Inter_PluckerAffineCover_aeval_of_mem_ker_c4e20c757a43
