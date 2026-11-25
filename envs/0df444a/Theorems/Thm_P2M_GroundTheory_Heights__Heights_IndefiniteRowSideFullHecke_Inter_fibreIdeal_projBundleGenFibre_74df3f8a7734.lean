-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreIdeal_projBundleGenFibre_74df3f8a7734
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreIdeal_projBundleGenFibre_74df3f8a7734
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:42.747877+00:00
-- url     : https://prove2.me/theorems/866fc96c-9369-5111-9228-71a28a749604
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter fibre Ideal proj Bundle Gen Fibre 74df3f8a7734: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter fibre
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter fibre Ideal proj Bundle Gen Fibre 74df3f8a7734 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter fibre Ideal proj Bundle Gen Fibre 74df3f8a7734 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleFibre.lean#L187-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleFibre.lean#L187-L210

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermOfIsPullHermInl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleFibre
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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreIdeal_projBundleGenFibre_74df3f8a7734 (P : Ideal (MRing ι)) [P.IsPrime] {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    fibreIdeal Sum.inl (projBundleGenFibre P B) =
      RingHom.ker (linSubst fun q a => B a (fibreCoordEquiv ι N1 q)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«fibreIdeal_projBundleGenFibre» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_fibreIdeal_projBundleGenFibre_74df3f8a7734
