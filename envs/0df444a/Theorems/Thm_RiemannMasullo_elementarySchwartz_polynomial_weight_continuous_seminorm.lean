-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartz_polynomial_weight_continuous_seminorm
-- name    : RiemannMasullo.elementarySchwartz_polynomial_weight_continuous_seminorm
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T03:32:25.279219+00:00
-- url     : https://prove2.me/theorems/eb2364a5-6f80-4741-9d64-31448adfb487
-- title:
--   Each polynomially weighted mixed-partial supremum defines a continuous elementary Schwartz seminorm
-- statement:
--   The supremum over all covering, lattice, and finite-group coordinates of a polynomial weight times a fixed mixed partial is finite and gives a continuous complex seminorm on the elementary Schwartz space.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L458-L468

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
open scoped ENNReal

namespace RiemannMasullo
theorem elementarySchwartz_polynomial_weight_continuous_seminorm (p : MvPolynomial (Fin m ⊕ Fin r) ℂ) (β : Fin m → ℕ) (γ : Fin n → ℕ) :
    ∃ q : Seminorm ℂ (ElementarySchwartz m n r F), Continuous q ∧ ∀ f, ENNReal.ofReal (q f) =
      ⨆ (x : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
        ENNReal.ofReal (‖MvPolynomial.eval (Sum.elim (fun k => (x.1 k : ℂ)) (fun k => (a k : ℂ))) p‖ *
          ‖elementaryPartial f β γ x a b‖) := by sorry
end RiemannMasullo
