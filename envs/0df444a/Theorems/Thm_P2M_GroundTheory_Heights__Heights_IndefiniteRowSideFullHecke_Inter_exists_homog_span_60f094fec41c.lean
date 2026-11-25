-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_homog_span_60f094fec41c
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_homog_span_60f094fec41c
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:22:39.357407+00:00
-- url     : https://prove2.me/theorems/6159d8cc-6693-4af1-ae85-ddddcfe6cd38
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists homog span 60f094fec41c: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists homog span 60f0
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists homog span 60f094fec41c construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter exists homog span 60f094fec41c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomogSpan.lean#L68-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomogSpan.lean#L68-L136

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ProjLineRankTwoPushforwardHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogGrad
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleMultiHomogSpan
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_homog_span_60f094fec41c [DecidableEq K] (P : Ideal (MRing ι)) [P.IsPrime]
    (hP : ∀ f ∈ P, ∀ b, weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f ∈ P)
    {t N1 n : ℕ} (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (hc : ∀ r j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (c r j) m)
    (B : Fin n → Fin N1 → FnField P)
    (hB : ∀ a, B a ∈ LinearMap.ker (Matrix.mulVecLin (Matrix.of fun r j => evalAt (genPt P) (c r j)))) :
    ∃ (S : Type) (_ : Fintype S) (V : S → Fin N1 → MRing ι) (γ : S → K → ℕ),
      (∀ s j, IsWeightedHomogeneous (NumbersDVR.blockWeight ι) (V s j) (γ s)) ∧
      (∀ s, (fun j => toFn P (V s j)) ∈
        LinearMap.ker (Matrix.mulVecLin (Matrix.of fun r j => evalAt (genPt P) (c r j)))) ∧
      ∀ a, B a ∈ Submodule.span (FnField P) (Set.range fun s j => toFn P (V s j)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«exists_homog_span» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_exists_homog_span_60f094fec41c
