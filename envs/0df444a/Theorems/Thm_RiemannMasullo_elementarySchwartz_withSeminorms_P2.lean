-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartz_withSeminorms_P2
-- name    : RiemannMasullo.elementarySchwartz_withSeminorms_P2
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T03:37:34.224349+00:00
-- url     : https://prove2.me/theorems/3d18d820-32a0-4f8e-bb66-8647c207515c
-- title:
--   Polynomial weights generate the elementary Schwartz topology
-- statement:
--   The suprema of mixed partial derivatives weighted by arbitrary complex coordinate polynomials give a defining seminorm family for the elementary Schwartz space.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L460-L467

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
open scoped ENNReal

namespace RiemannMasullo

theorem elementarySchwartz_withSeminorms_P2 :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F)
        ((Fin m → ℕ) × (Fin n → ℕ) × MvPolynomial (Fin m ⊕ Fin r) ℂ),
      WithSeminorms p ∧ ∀ i f, ENNReal.ofReal (p i f) =
        ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
          ENNReal.ofReal
            (‖MvPolynomial.eval (Sum.elim (fun k ↦ (xt.1 k : ℂ)) (fun k ↦ (a k : ℂ))) i.2.2‖ *
              ‖elementaryPartial f i.1 i.2.1 xt a b‖) := by sorry

end RiemannMasullo
