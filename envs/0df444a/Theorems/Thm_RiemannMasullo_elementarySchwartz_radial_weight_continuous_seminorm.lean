-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartz_radial_weight_continuous_seminorm
-- name    : RiemannMasullo.elementarySchwartz_radial_weight_continuous_seminorm
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T04:18:50.983415+00:00
-- url     : https://prove2.me/theorems/fc123ae2-0e68-457d-8bae-aac1784c86a0
-- title:
--   Continuity of all radial Schwartz seminorms
-- statement:
--   The supremum of a fixed mixed derivative multiplied by radial weights of any two nonnegative integer degrees defines a continuous seminorm.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L447-L456

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]
open scoped ENNReal

namespace RiemannMasullo
theorem elementarySchwartz_radial_weight_continuous_seminorm (k l : ℕ) (β : Fin m → ℕ) (γ : Fin n → ℕ) :
    ∃ q : Seminorm ℂ (ElementarySchwartz m n r F), Continuous q ∧ ∀ f, ENNReal.ofReal (q f) =
      ⨆ (x : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
        ENNReal.ofReal ((1+‖x.1‖^k)*(1+‖(WithLp.toLp 2 (fun j => (a j : ℝ)) :
          EuclideanSpace ℝ (Fin r))‖^l)*‖elementaryPartial f β γ x a b‖) := by sorry
end RiemannMasullo
