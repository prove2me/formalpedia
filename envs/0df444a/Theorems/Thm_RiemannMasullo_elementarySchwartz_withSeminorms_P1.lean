-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartz_withSeminorms_P1
-- name    : RiemannMasullo.elementarySchwartz_withSeminorms_P1
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T04:20:31.147368+00:00
-- url     : https://prove2.me/theorems/8c33a3c9-c1de-47cf-939c-bf2a64e9ea17
-- title:
--   Radial weights generate the elementary Schwartz topology
-- statement:
--   Suprema of mixed partial derivatives weighted by powers of the two Euclidean lengths give a defining family of seminorms.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L449-L456

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
open scoped ENNReal
open Filter Topology

namespace RiemannMasullo

theorem elementarySchwartz_withSeminorms_P1 :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F)
        (ℕ × ℕ × (Fin m → ℕ) × (Fin n → ℕ)),
      WithSeminorms p ∧ ∀ i f, ENNReal.ofReal (p i f) =
        ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
          ENNReal.ofReal ((1 + ‖xt.1‖ ^ i.1) *
            (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ i.2.1) *
            ‖elementaryPartial f i.2.2.1 i.2.2.2 xt a b‖) := by sorry

end RiemannMasullo
