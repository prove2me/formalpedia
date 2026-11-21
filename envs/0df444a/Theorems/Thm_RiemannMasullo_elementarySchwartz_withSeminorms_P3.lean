-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartz_withSeminorms_P3
-- name    : RiemannMasullo.elementarySchwartz_withSeminorms_P3
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T03:58:01.452749+00:00
-- url     : https://prove2.me/theorems/888c7ba9-2ce1-49fb-8494-24203454573b
-- title:
--   Polynomial differential operators generate the elementary Schwartz topology
-- statement:
--   Supremum seminorms formed from constant-coefficient polynomial differential operators and coordinate polynomial weights generate the elementary Schwartz topology.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L471-L478

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
open scoped ENNReal

namespace RiemannMasullo

theorem elementarySchwartz_withSeminorms_P3 :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F)
        (MvPolynomial (Fin m ⊕ Fin r) ℂ × MvPolynomial (Fin m ⊕ Fin n) ℂ),
      WithSeminorms p ∧ ∀ i f, ENNReal.ofReal (p i f) =
        ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
          (‖MvPolynomial.eval (Sum.elim (fun k ↦ (xt.1 k : ℂ)) (fun k ↦ (a k : ℂ))) i.1 *
            (∑ d ∈ i.2.support, i.2.coeff d * elementaryPartial f
              (fun k ↦ d (.inl k)) (fun k ↦ d (.inr k)) xt a b)‖₊ : ℝ≥0∞) := by sorry

end RiemannMasullo
