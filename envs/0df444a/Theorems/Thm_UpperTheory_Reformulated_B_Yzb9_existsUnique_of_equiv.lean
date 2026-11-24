-- Prove2me | Theorems.Thm_UpperTheory_Reformulated_B_Yzb9_existsUnique_of_equiv
-- name    : UpperTheory.Reformulated.B.Yzb9.existsUnique_of_equiv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:56:54.111638+00:00
-- url     : https://prove2.me/theorems/a9cb432e-b773-42a7-9a7c-e3bcde9d176d
-- title:
--   Yzb9: exists Unique of equiv
-- statement:
--   The Yzb9 construction uses the exists Unique of equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralCompContinuousLinearEquiv.lean#L245-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/IntegralCompContinuousLinearEquiv.lean#L245-L301

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_IntegralCompContinuousLinearEquiv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem UpperTheory.Reformulated.B.Yzb9.existsUnique_of_equiv :
    ∀ {V W : Type} [inst : AddCommGroup V] [inst_1 : TopologicalSpace V] [IsTopologicalAddGroup V]
      [inst_3 : MeasurableSpace V] [BorelSpace V] [inst_5 : NormedAddCommGroup W] [inst_6 : NormedSpace ℝ W]
      [FiniteDimensional ℝ W] (e : V ≃+ W),
      Continuous (⇑e : V → W) →
        Continuous (⇑e.symm : W → V) →
          ∀ (l : V → V → ℝ),
            (∀ (x x' y : V), l (x + x') y = l x y + l x' y) →
              (∀ (x y : V), l x y = l y x) →
                (∀ (y : V), Continuous fun (x : V) ↦ l x y) →
                  (∀ (x : V), (∀ (y : V), l x y = (0 : ℝ)) → x = (0 : V)) →
                    ∃! μ : MeasureTheory.Measure V,
                      UpperTheory.Reformulated.B.Yzb9.SelfDual μ fun (x y : V) ↦
                        Complex.exp ((2 : ℂ) * (↑Real.pi : ℂ) * Complex.I * (↑(l x y) : ℂ)) := by sorry
