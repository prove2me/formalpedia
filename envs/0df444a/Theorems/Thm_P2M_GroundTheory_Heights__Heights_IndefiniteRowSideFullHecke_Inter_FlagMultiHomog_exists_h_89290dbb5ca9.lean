-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_exists_h_89290dbb5ca9
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_exists_h_89290dbb5ca9
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:26:11.330007+00:00
-- url     : https://prove2.me/theorems/26b3089c-7344-5d8e-b3ac-516afb4ba5c0
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi Homog exists h 89290dbb5ca9: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi Hom
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi Homog exists h 89290dbb5ca9 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi Homog exists h 89290dbb5ca9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMultiHomog.lean#L200-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMultiHomog.lean#L200-L221

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StFlagMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveComplexPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagMultiHomog
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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagMultiHomog
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {N1 n : ℕ}
omit [DecidableEq K]

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_exists_h_89290dbb5ca9 (P : Ideal (MRing ι)) [P.IsPrime] {t : ℕ} (c : Fin t → Fin N1 → MRing ι) (m : K → ℕ)
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (hc : ∀ a j, IsMultiHomog (c a j) m) (hB : IsKerBasis P c B)
    (σ : FnField P →+* OmegaF P n)
    (hσ : ∀ p : Σ k, ι k, σ (genPt P p) = iota P n (genPt P p) * lam P n (Sum.inl p.1)) :
    ∃ h : Matrix (Fin n) (Fin n) (OmegaF P n), h * B.map σ = B.map (iota P n) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«FlagMultiHomog».«exists_h» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_exists_h_89290dbb5ca9
