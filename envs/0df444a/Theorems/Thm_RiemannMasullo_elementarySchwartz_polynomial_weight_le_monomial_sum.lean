-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartz_polynomial_weight_le_monomial_sum
-- name    : RiemannMasullo.elementarySchwartz_polynomial_weight_le_monomial_sum
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T03:29:21.601062+00:00
-- url     : https://prove2.me/theorems/7b03918a-e0f2-4997-9615-e94c0d250d4a
-- title:
--   A polynomially weighted mixed partial is bounded by the coefficient-weighted monomial seminorms
-- statement:
--   Evaluating a complex polynomial in the continuous and discrete coordinates and multiplying by a fixed mixed partial is bounded by the sum over its support of coefficient norms times the matching elementary Schwartz seminorms.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L458-L468

import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
import Mathlib
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

namespace RiemannMasullo
theorem elementarySchwartz_polynomial_weight_le_monomial_sum (p : MvPolynomial (Fin m ⊕ Fin r) ℂ) (f : ElementarySchwartz m n r F)
    (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    ‖MvPolynomial.eval (Sum.elim (fun k => (xt.1 k : ℂ)) (fun k => (a k : ℂ))) p‖ *
      ‖elementaryPartial f β γ xt a b‖ ≤
    ∑ d ∈ p.support, ‖p.coeff d‖ * elementarySchwartzSeminorm
      (fun k => d (Sum.inl k), β, γ, fun k => d (Sum.inr k)) f := by sorry
end RiemannMasullo
