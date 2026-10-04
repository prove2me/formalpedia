-- Prove2me | Theorems.Thm_ThompsonAmenability_not_isCoamenable_HRat
-- name    : ThompsonAmenability.not_isCoamenable_HRat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-30T18:55:21.4455+00:00
-- url     : https://prove2.me/theorems/f6f3086e-c263-4840-ae45-8d3768319c6b
-- title:
--   Monod 2023, Theorem 5.1 — the Thompson group H_ℚ(ℤ) is not co-amenable in H_ℚ(ℚ), nor in its C¹ subgroup
-- statement:
--   Let $H_{\mathbf Q}(\mathbf Z)$ and $H_{\mathbf Q}(\mathbf Q)$ be the groups of homeomorphisms of the line that are piecewise in $\mathrm{SL}_2(\mathbf Z)$, respectively $\mathrm{SL}_2(\mathbf Q)$, with rational breakpoints (`Monod.HRat`, from the Monod bundle, and `HB ratSubring Monod.ratPoints`), and let $H^{C^1}_{\mathbf Q}(\mathbf Q)$ (`HC1RatRat`) be the subgroup of $H_{\mathbf Q}(\mathbf Q)$ of $C^1$-diffeomorphisms. Then $H_{\mathbf Q}(\mathbf Z)$ is a subgroup of $H_{\mathbf Q}(\mathbf Q)$ and of $H^{C^1}_{\mathbf Q}(\mathbf Q)$, and is co-amenable in neither: neither coset space carries an invariant mean (`Monod.IsCoamenable`).
--
--   **Formalization Note.** The two containments $H_{\mathbf Q}(\mathbf Z) \le H_{\mathbf Q}(\mathbf Q)$ and $H_{\mathbf Q}(\mathbf Z) \le H^{C^1}_{\mathbf Q}(\mathbf Q)$ are implicit in "not co-amenable in" (the second also in the remark on p. 14 that the elements of $H_{\mathbf Q}(\mathbf Z)$ are "actually $C^1$-smooth") and are stated. Monod calls $H_{\mathbf Q}(\mathbf Z)$ the Thompson group: it is isomorphic to $F$, an observation Monod attributes to Thurston (p. 3), and a published result of the Monod mission (`Monod.contDiff_and_exists_mulEquiv_HRat_F`). Neither that isomorphism nor the properness of $H^{C^1}_{\mathbf Q}(\mathbf Q)$ in $H_{\mathbf Q}(\mathbf Q)$ ("the smaller subgroup") is part of the formal statement.
-- source:
--   Monod, N., Some comments on piecewise-projective groups of the line, Groups Geom. Dyn. 19 (2025) 459–476, https://doi.org/10.4171/ggd/883 (arXiv:2305.00796, whose page numbers are used), p. 14, Theorem 5.1

import Mathlib
import Definitions.Def_Monod_PiecewiseProjective
import Definitions.Def_ThompsonAmenability

namespace ThompsonAmenability

theorem not_isCoamenable_HRat :
    (Monod.HRat ≤ HB ratSubring Monod.ratPoints ∧
      ¬ Monod.IsCoamenable (Monod.HRat.subgroupOf (HB ratSubring Monod.ratPoints))) ∧
    (Monod.HRat ≤ HC1RatRat ∧ ¬ Monod.IsCoamenable (Monod.HRat.subgroupOf HC1RatRat)) := by
  sorry

end ThompsonAmenability
