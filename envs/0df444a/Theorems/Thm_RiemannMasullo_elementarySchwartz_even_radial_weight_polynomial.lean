-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartz_even_radial_weight_polynomial
-- name    : RiemannMasullo.elementarySchwartz_even_radial_weight_polynomial
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T04:18:02.276183+00:00
-- url     : https://prove2.me/theorems/abf5fd4d-66d0-48fe-822f-09b194fdd401
-- title:
--   Even radial Schwartz weights are coordinate polynomials
-- statement:
--   Products of one plus an even power of each Euclidean norm are evaluations of a single complex coordinate polynomial.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L447-L456

import Mathlib

namespace RiemannMasullo
theorem elementarySchwartz_even_radial_weight_polynomial {m r : ℕ} (k l : ℕ) :
    ∃ p : MvPolynomial (Fin m ⊕ Fin r) ℂ,
      ∀ (x : EuclideanSpace ℝ (Fin m)) (y : EuclideanSpace ℝ (Fin r)),
      MvPolynomial.eval (Sum.elim (fun i => (x i : ℂ)) (fun j => (y j : ℂ))) p =
        (((1+‖x‖^(2*k))*(1+‖y‖^(2*l)) : ℝ) : ℂ) := by sorry
end RiemannMasullo
