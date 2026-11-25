-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_genMap_le_7f717af17469
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_genMap_le_7f717af17469
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:33.146424+00:00
-- url     : https://prove2.me/theorems/a946b54e-b797-5124-814f-b5e4994cbb1b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter ker gen Map le 7f717af17469: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter ker gen Map le 7f717af174
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter ker gen Map le 7f717af17469 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter ker gen Map le 7f717af17469 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomogSpan.lean#L39-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleMultiHomogSpan.lean#L39-L64

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
omit [Fintype K] [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_genMap_le_7f717af17469 (P : Ideal (MRing ι)) {N1 : ℕ} {S S' : Type} [Fintype S] [Fintype S']
    (v : S → Fin N1 → FnField P) (v' : S' → Fin N1 → FnField P)
    (h : ∀ s', v' s' ∈ Submodule.span (FnField P) (Set.range v)) :
    RingHom.ker (genMap P v) ≤ RingHom.ker (genMap P v') := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«ker_genMap_le» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_genMap_le_7f717af17469
