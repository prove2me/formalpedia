-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_rename_inlV_mem_projBundleIdeal_iff_c30f3fd57594
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_rename_inlV_mem_projBundleIdeal_iff_c30f3fd57594
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:44:58.003325+00:00
-- url     : https://prove2.me/theorems/2fd052b2-8488-41d9-b635-50dbb9fc7e2a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter rename inl V mem proj Bundle Ideal iff c30f3fd57594: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter r
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter rename inl V mem proj Bundle Ideal iff c30f3fd57594 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter rename inl V mem proj Bundle Ideal iff c30f3fd57594 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleArith.lean#L21-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleArith.lean#L21-L25

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermOfIsPullHermInl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleArith
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_rename_inlV_mem_projBundleIdeal_iff_c30f3fd57594 (P : Ideal (MRing ι)) {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (f : MRing ι) :
    rename (inlV (ι₂ := fun _ : Unit => Fin N1)) f ∈ projBundleIdeal P B ↔ f ∈ P := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«rename_inlV_mem_projBundleIdeal_iff» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_rename_inlV_mem_projBundleIdeal_iff_c30f3fd57594
