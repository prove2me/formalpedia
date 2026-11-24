-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_val_pair_5c72587972df
-- name    : P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_val_pair_5c72587972df
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:51.874255+00:00
-- url     : https://prove2.me/theorems/028ea293-5ec5-4bff-97d8-f7a476013c63
-- title:
--   P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor val pair 5c72587972df: P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor val pair 5c72587972df
-- statement:
--   The P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor val pair 5c72587972df construction uses the P2 M Ground Theory Heights  Heights Numbers DVR Generic Proj Closure Divisor val pair 5c72587972df property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L283-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/PGenericProjClosureDivisor.lean#L283-L290

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsGenericProjClosureDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsTwistedDualGensExpress
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDivisor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.GenericProjClosureDivisor
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
  {N M M' : ℕ} {E : Type} [AddCommGroup E] [Module Ω E]
  {Φ : Type} [Field Φ] [Algebra Ω Φ] [Algebra O Φ] [IsScalarTower O Ω Φ]
variable [∀ k, Fintype (ι k)]
omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] [Algebra O Ω] [IsScalarTower O Ω Φ]

theorem P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_val_pair_5c72587972df {z : (Σ o, bundleIdx (bundleIdx ι M) M' o) → Φ} {L : ℕ}
    {xs : Fin L → MRing (bundleIdx (bundleIdx ι M) M') O} {v : Fin L → Φ} (hxs : ∀ l, aeval z (xs l) = v l)
    (G : Fin L → MRing (bundleIdx (bundleIdx ι M) M') O) {x : MRing (bundleIdx (bundleIdx ι M) M') O} {w : Φ}
    (hx : aeval z x = w) (H : MRing (bundleIdx (bundleIdx ι M) M') O)
    (hval : aeval z H * w = ∑ l, aeval z (G l) * v l) :
    aeval z (∑ l, xs l * G l) = aeval z (x * H) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«NumbersDVR».«GenericProjClosureDivisor».«val_pair» := P2M_GroundTheory_Heights__Heights_NumbersDVR_GenericProjClosureDivisor_val_pair_5c72587972df
