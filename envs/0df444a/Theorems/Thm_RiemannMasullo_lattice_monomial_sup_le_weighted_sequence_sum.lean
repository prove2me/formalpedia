-- Prove2me | Theorems.Thm_RiemannMasullo_lattice_monomial_sup_le_weighted_sequence_sum
-- name    : RiemannMasullo.lattice_monomial_sup_le_weighted_sequence_sum
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T03:09:32.277035+00:00
-- url     : https://prove2.me/theorems/f36cde90-4b68-4e6e-871c-87bbb644d768
-- title:
--   Every lattice monomial supremum is bounded by the weighted absolute sum of its total degree
-- statement:
--   Pulling a lattice sequence back to the discrete elementary Lie group, its monomial Schwartz supremum of multi-degree d is at most its weighted absolute sum of order |d|. This holds for arbitrary sequences in the extended nonnegative reals.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L604-L606

import Definitions.Def_RiemannMasullo_ElementarySchwartzBounds
import Definitions.Def_RiemannMasullo_RapidDecaySequenceBound
import Mathlib
open RiemannMasullo
open scoped ENNReal NNReal

namespace RiemannMasullo
theorem lattice_monomial_sup_le_weighted_sequence_sum (r : ℕ) (s : (Fin r → ℤ) → ℂ) (i : ElementarySchwartzIndex 0 0 r) :
    elementarySchwartzBound (fun g : ElementaryLieGroup 0 0 r PUnit => s g.2.2.1) i ≤
      rapidDecaySequenceBound (∑ k, i.2.2.2 k) s := by sorry
end RiemannMasullo
