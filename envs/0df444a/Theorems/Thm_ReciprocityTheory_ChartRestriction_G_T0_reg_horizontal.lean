-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_reg_horizontal
-- name    : ReciprocityTheory.ChartRestriction.G.T0.reg_horizontal
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:39:21.363148+00:00
-- url     : https://prove2.me/theorems/131f2e29-1684-4fb4-9d5a-085690110034
-- title:
--   T0: reg horizontal
-- statement:
--   The T0 construction uses the reg horizontal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegHor.lean#L8-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegHor.lean#L8-L21

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegHorPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegHor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open IsLocalRing

theorem ReciprocityTheory.ChartRestriction.G.T0.reg_horizontal {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    (P : Ideal A) [P.IsPrime] (hh : ¬ Ideal.map (algebraMap O A) (maximalIdeal O) ≤ P)
    (hmeet : P ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤) (e : A) (he : e ≠ 0)
    (f : FractionRing A)
    (hdvr : (¬ ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a) →
      ∃ a s : A, a ∈ P ∧ s ∉ P ∧ f⁻¹ * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V) (a b : A),
      f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a → φ b ≠ 0 → φ e ≠ 0 →
      ∃ v : V, φ a = v * φ b) :
    ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by sorry
