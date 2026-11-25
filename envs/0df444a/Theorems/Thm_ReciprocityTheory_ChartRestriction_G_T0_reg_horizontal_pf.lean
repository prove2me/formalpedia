-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_reg_horizontal_pf
-- name    : ReciprocityTheory.ChartRestriction.G.T0.reg_horizontal_pf
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:38:57.439894+00:00
-- url     : https://prove2.me/theorems/42cbdc43-f3af-503d-9c28-49552dd099ef
-- title:
--   T0: reg horizontal pf
-- statement:
--   The T0 construction uses the reg horizontal pf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegHorPf.lean#L22-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegHorPf.lean#L22-L195

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegAVpt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegHorPf
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

theorem ReciprocityTheory.ChartRestriction.G.T0.reg_horizontal_pf {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
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
