-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_reg_vertical
-- name    : ReciprocityTheory.ChartRestriction.G.T0.reg_vertical
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T14:15:40.802923+00:00
-- url     : https://prove2.me/theorems/7765879a-6cf9-4222-aafa-6a9f26b0689b
-- title:
--   T0: reg vertical
-- statement:
--   The T0 construction uses the reg vertical property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegVert.lean#L101-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/RegVert.lean#L101-L233

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegAVpt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_RegVert
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

theorem ReciprocityTheory.ChartRestriction.G.T0.reg_vertical {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    [IsIntegrallyClosed A] (f : FractionRing A)
    (hf : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V) (a b : A),
      f * algebraMap A (FractionRing A) b = algebraMap A (FractionRing A) a → φ b ≠ 0 →
      ∃ v : V, φ a = v * φ b)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (hv : Ideal.map (algebraMap O A) (maximalIdeal O) ≤ P) :
    ∃ a s : A, s ∉ P ∧ f * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by sorry
