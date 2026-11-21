-- Prove2me | Theorems.Thm_RiemannMasullo_elementarySchwartz_withSeminorms_sum
-- name    : RiemannMasullo.elementarySchwartz_withSeminorms_sum
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-21T03:05:53.690178+00:00
-- url     : https://prove2.me/theorems/10c17657-163b-4696-bbda-6898acb45e5d
-- title:
--   Increasing-degree sums of the elementary Schwartz seminorms generate the topology
-- statement:
--   Finite sums of all the prescribed monomial seminorms through each degree bound are norms and generate the elementary Schwartz topology.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppD_SchwartzBruhat/Sec1a.lean#L482-L493

import Mathlib
import Definitions.Def_RiemannMasullo_ElementarySchwartzTopology
open RiemannMasullo
variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

namespace RiemannMasullo

theorem elementarySchwartz_withSeminorms_sum :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F) ℕ,
      WithSeminorms p ∧ (∀ N f, p N f = 0 ↔ f = 0) ∧
        ∀ N f, p N f =
          ∑ i : (Fin m → Fin (N + 1)) × (Fin m → Fin (N + 1)) ×
                (Fin n → Fin (N + 1)) × (Fin r → Fin (N + 1)),
            if (∑ k, (i.1 k).val) ≤ N ∧ (∑ k, (i.2.1 k).val) ≤ N ∧
                (∑ k, (i.2.2.1 k).val) ≤ N ∧ (∑ k, (i.2.2.2 k).val) ≤ N then
              elementarySchwartzSeminorm
                (fun k ↦ (i.1 k).val, fun k ↦ (i.2.1 k).val,
                  fun k ↦ (i.2.2.1 k).val, fun k ↦ (i.2.2.2 k).val) f
            else 0 := by sorry

end RiemannMasullo
