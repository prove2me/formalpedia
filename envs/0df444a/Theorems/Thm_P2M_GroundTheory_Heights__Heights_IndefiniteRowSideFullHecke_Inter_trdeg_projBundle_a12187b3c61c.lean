-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_trdeg_projBundle_a12187b3c61c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_trdeg_projBundle_a12187b3c61c
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:24:03.272958+00:00
-- url     : https://prove2.me/theorems/ea770115-4e1f-48e8-b9b4-0e69efc7818a
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter trdeg proj Bundle a12187b3c61c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter trdeg proj Bundle a121
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter trdeg proj Bundle a12187b3c61c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter trdeg proj Bundle a12187b3c61c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleDim.lean#L54-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleDim.lean#L54-L131

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_trdeg_projBundle_a12187b3c61c (P : Ideal (MRing ι)) [P.IsPrime] (hPz : IsHorizontal P) {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (hB : LinearIndependent (FnField P) B) :
    Algebra.trdeg ℤ (MRing (PBlk ι N1) ⧸ projBundleIdeal P B) =
      Algebra.trdeg ℤ (MRing ι ⧸ P) + n := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«trdeg_projBundle» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_trdeg_projBundle_a12187b3c61c
