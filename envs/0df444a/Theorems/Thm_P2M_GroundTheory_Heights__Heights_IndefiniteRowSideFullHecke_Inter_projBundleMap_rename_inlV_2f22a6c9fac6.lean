-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projBundleMap_rename_inlV_2f22a6c9fac6
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projBundleMap_rename_inlV_2f22a6c9fac6
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:30:11.415949+00:00
-- url     : https://prove2.me/theorems/94919712-dd52-5234-9531-81fa277b2f4e
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj Bundle Map rename inl V 2f22a6c9fac6: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj Bundle
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj Bundle Map rename inl V 2f22a6c9fac6 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter proj Bundle Map rename inl V 2f22a6c9fac6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleDim.lean#L31-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleDim.lean#L31-L48

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_StatementsIntDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleDim
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
variable {K : Type} {ι : K → Type}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projBundleMap_rename_inlV_2f22a6c9fac6 (P : Ideal (MRing ι)) {N1 n : ℕ} (B : Matrix (Fin n) (Fin N1) (FnField P))
    (g : MRing ι) :
    projBundleMap P B (rename (inlV (ι₂ := fun _ : Unit => Fin N1)) g) =
      C (algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P g)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«projBundleMap_rename_inlV» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_projBundleMap_rename_inlV_2f22a6c9fac6
