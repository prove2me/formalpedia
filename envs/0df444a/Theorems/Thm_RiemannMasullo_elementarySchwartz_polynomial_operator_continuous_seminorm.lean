-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartz_polynomial_operator_continuous_seminorm
-- name    : RiemannMasullo.elementarySchwartz_polynomial_operator_continuous_seminorm
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T03:58:58.562149+00:00
-- url     : https://prove2.me/theorems/563fd9d0-f420-49aa-bebc-535db32ea5a2
-- title:
--   Continuity of polynomial differential operator seminorms on the elementary Schwartz space
-- statement:
--   Each polynomial-weighted constant-coefficient differential operator gives a continuous supremum seminorm.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L471-L478

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
open scoped ENNReal

namespace RiemannMasullo
theorem elementarySchwartz_polynomial_operator_continuous_seminorm (p : MvPolynomial (Fin m ⊕ Fin r) ℂ) (D : MvPolynomial (Fin m ⊕ Fin n) ℂ) :
    ∃ q : Seminorm ℂ (ElementarySchwartz m n r F), Continuous q ∧ ∀ f, ENNReal.ofReal (q f) =
      ⨆ (x : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
        (‖MvPolynomial.eval (Sum.elim (fun k => (x.1 k : ℂ)) (fun k => (a k : ℂ))) p *
          (∑ d ∈ D.support, D.coeff d * elementaryPartial f (fun k => d (.inl k)) (fun k => d (.inr k)) x a b)‖₊ : ℝ≥0∞) := by sorry
end RiemannMasullo
