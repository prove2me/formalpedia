-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_cycEval_divCycle_eq_56b97df708b1
-- name    : P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_cycEval_divCycle_eq_56b97df708b1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:07:14.08317+00:00
-- url     : https://prove2.me/theorems/341ca93a-fa3d-40b2-8b75-3e1c62d6de97
-- title:
--   P2 M Ground Theory Heights  Heights Bridge Geo Num cyc Eval div Cycle eq 56b97df708b1: P2 M Ground Theory Heights  Heights Bridge Geo Num cyc Eval div Cycle eq 56b97df708b1
-- statement:
--   The P2 M Ground Theory Heights  Heights Bridge Geo Num cyc Eval div Cycle eq 56b97df708b1 construction uses the P2 M Ground Theory Heights  Heights Bridge Geo Num cyc Eval div Cycle eq 56b97df708b1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L80-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/GeoNum.lean#L80-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Assembly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PIntNumPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSpecialMultAt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_GeoNum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Bridge
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.Bridge.GeoNum
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable (p : ℕ) [Fact p.Prime]

theorem P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_cycEval_divCycle_eq_56b97df708b1 (Q : Ideal (MRing ι (ZMod p))) (s : MRing ι ℤ)
    (N : Ideal (MRing ι (ZMod p)) → ℤ) (g : Ideal (MRing ι ℤ) → ℤ)
    (h : ∀ W', divCycle Q (red p s) W' ≠ 0 → N W' = g (W'.comap (red p))) :
    cycEval N (divCycle Q (red p s)) =
      ∑ᶠ W ∈ Geo.divSupp (Q.comap (red p)) s,
        (Geo.multAt (Q.comap (red p) ⊔ Ideal.span {s}) W : ℤ) * g W := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Bridge».«GeoNum».«cycEval_divCycle_eq» := P2M_GroundTheory_Heights__Heights_Bridge_GeoNum_cycEval_divCycle_eq_56b97df708b1
