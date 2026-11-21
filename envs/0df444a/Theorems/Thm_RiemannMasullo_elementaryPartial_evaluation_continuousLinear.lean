-- Prove2me | Theorems.Thm_RiemannMasullo_elementaryPartial_evaluation_continuousLinear
-- name    : RiemannMasullo.elementaryPartial_evaluation_continuousLinear
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T03:30:53.465377+00:00
-- url     : https://prove2.me/theorems/3c449375-a891-4431-97c5-c79045898fb7
-- title:
--   Evaluation of each mixed partial is a continuous complex-linear Schwartz functional
-- statement:
--   At each fixed covering point, lattice point, and finite-group component, the specified mixed partial acts continuously and complex-linearly on elementary Schwartz functions.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L283-L293

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

namespace RiemannMasullo
theorem elementaryPartial_evaluation_continuousLinear (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (x : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    ∃ L : ElementarySchwartz m n r F →L[ℂ] ℂ, ∀ f, L f = elementaryPartial f β γ x a b := by sorry
end RiemannMasullo
