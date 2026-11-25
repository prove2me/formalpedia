-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_sigma_evalAt_ac9e324bd051
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_sigma_evalAt_ac9e324bd051
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:28.761453+00:00
-- url     : https://prove2.me/theorems/d5c44c70-23b2-5916-9c65-bb9b68f7bb9b
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi Homog sigma eval At ac9e324bd051: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Mult
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi Homog sigma eval At ac9e324bd051 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter Flag Multi Homog sigma eval At ac9e324bd051 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMultiHomog.lean#L181-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PFlagMultiHomog.lean#L181-L196

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

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_sigma_evalAt_ac9e324bd051 (P : Ideal (MRing ι)) [P.IsPrime] (n : ℕ) (σ : FnField P →+* OmegaF P n)
    (hσ : ∀ p : Σ k, ι k, σ (genPt P p) = iota P n (genPt P p) * lam P n (Sum.inl p.1))
    {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    σ (evalAt (genPt P) f) = (∏ k, lam P n (Sum.inl k) ^ a k) * iota P n (evalAt (genPt P) f) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«FlagMultiHomog».«sigma_evalAt» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagMultiHomog_sigma_evalAt_ac9e324bd051
