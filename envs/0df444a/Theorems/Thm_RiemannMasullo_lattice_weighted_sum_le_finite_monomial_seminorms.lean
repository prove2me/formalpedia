-- Prove2me | Theorems.Thm_RiemannMasullo_lattice_weighted_sum_le_finite_monomial_seminorms
-- name    : RiemannMasullo.lattice_weighted_sum_le_finite_monomial_seminorms
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T03:17:50.726609+00:00
-- url     : https://prove2.me/theorems/f80cd32a-b929-4e12-98b0-d1e6380c9894
-- title:
--   A finite sum of lattice monomial seminorms bounds each weighted ℓ¹ seminorm
-- statement:
--   Each order-j weighted absolute sum of a discrete elementary Schwartz function is bounded by a fixed constant times the sum of its monomial seminorms with exponents 0 or j+2. The constant is independent of the function.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L604-L606

import Definitions.Def_RiemannMasullo_RapidDecaySequenceTopology
import Mathlib
open RiemannMasullo
open scoped ENNReal

namespace RiemannMasullo
theorem lattice_weighted_sum_le_finite_monomial_seminorms (r j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ElementarySchwartz 0 0 r PUnit,
      rapidDecaySequenceBound j (fun a => f (0,0,a,PUnit.unit)) ≤
        ENNReal.ofReal (C * ∑ U : Finset (Fin r), elementarySchwartzSeminorm
          (0,0,0, fun i => if i ∈ U then j+2 else 0) f) := by sorry
end RiemannMasullo
