-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_linSubst_3544d063a3f5
-- name    : P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_linSubst_3544d063a3f5
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:40:22.015112+00:00
-- url     : https://prove2.me/theorems/8f5bd413-38ed-517d-8d4f-3e92c0d9c6c7
-- title:
--   P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter ker lin Subst 3544d063a3f5: P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter ker lin Subst 3544d063a3f5
-- statement:
--   The P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter ker lin Subst 3544d063a3f5 construction uses the P2 M Ground Theory Heights  Heights Indefinite Row Side Full Hecke Inter ker lin Subst 3544d063a3f5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleFibre.lean#L36-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/PProjBundleFibre.lean#L36-L70

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
variable {Φ : Type} [Field Φ] {σ : Type} [Fintype σ] {n : ℕ}

theorem P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_linSubst_3544d063a3f5 (ℓ : σ → Fin n → Φ) (ν : Fin n → σ → Φ)
    (hν : ∀ a b, ∑ q, ν a q * ℓ q b = if a = b then 1 else 0) :
    RingHom.ker (linSubst ℓ) = Ideal.span (linKerForms ℓ) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IndefiniteRowSideFullHecke».«Inter».«ker_linSubst» := P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_ker_linSubst_3544d063a3f5
