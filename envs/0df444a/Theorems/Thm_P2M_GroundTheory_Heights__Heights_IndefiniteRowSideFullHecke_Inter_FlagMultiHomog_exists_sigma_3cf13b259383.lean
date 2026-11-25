-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_exists_sigma_3cf13b259383
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_exists_sigma_3cf13b259383
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:23:08.921227+00:00
-- url     : https://prove2.me/theorems/a0e1e4f8-964a-4dfc-b920-21ffe1e136e6
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi Homog exists sigma 3cf13b259383: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi Homog exists sigma 3cf13b259383 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi Homog exists sigma 3cf13b259383 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMultiHomog.lean#L160-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMultiHomog.lean#L160-L177

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_exists_sigma_3cf13b259383 (P : Ideal (MRing ι)) [P.IsPrime] (hP : IsMultiHomogIdeal P) (n : ℕ) :
    ∃ σ : FnField P →+* OmegaF P n, ∀ p : Σ k, ι k,
      σ (genPt P p) = iota P n (genPt P p) * lam P n (Sum.inl p.1) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«FlagMultiHomog».«exists_sigma» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_exists_sigma_3cf13b259383
