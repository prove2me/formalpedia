-- Prove2me | Theorems.Thm_SubnormalCover_card_cosets_biUnion_ge
-- name    : SubnormalCover.card_cosets_biUnion_ge
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-14T12:44:49.727334+00:00
-- url     : https://prove2.me/theorems/1ae41b90-daa2-420c-bc20-0d0c241536e4
-- title:
--   Lower bound for the number of cosets in a union of cosets
-- statement:
--   Let $G$ be a group and $H \le G$ a subgroup of **finite index** $[G:H]$, and let $G_1,\dots,G_k$ be subgroups of $G$ that each **contain $H$** and are **subnormal in $G$**. Then for any $a_1,\dots,a_k\in G$,
--   $$\bigl|\{\,xH : x\in a_iG_i \text{ for some } i\,\}\bigr| \;\ge\; \bigl|\{\,0\le n<[G:H] : [G:G_i]\mid n \text{ for some } i\,\}\bigr|,$$
--   equivalently $\bigl[\bigcup_{i=1}^{k} a_iG_i : H\bigr] \ge \bigl[\bigcup_{i=1}^{k}[G:G_i]\mathbb{Z} : [G:H]\mathbb{Z}\bigr]$ — this is eq. (3.1) of Sun's Theorem 3.1, restricted to the subnormal branch (the alternative branch, where a composition series from $H$ to $G$ has prime-order quotients, is the pyramidal case handled elsewhere). Specialised to $G=\mathbb{Z}$ it recovers C. A. Rogers' theorem on residue classes, eq. (3.6).
--
--   **Formalization note.** $H$ is *not* assumed normal, so $G ⧸ H$ is used purely as a type of left cosets and the left-hand side is rendered as `Set.ncard` of the image of $\bigcup_i a_i G_i$ under `QuotientGroup.mk` (this counts the $H$-cosets that *meet* the union, which coincides with those *contained in* it exactly because $H \le G_i$ for all $i$); `Nat.card (G ⧸ H) = H.index` holds by `rfl`. Finiteness of $[G:H]$ is spelled `H.index ≠ 0` rather than as the `Subgroup.FiniteIndex` instance, and the right-hand side is the cardinality of `(Finset.range H.index).filter (fun n => ∃ i, (K i).index ∣ n)`.
-- source:
--   Z.-W. Sun, On the Herzog-Schönheim conjecture for uniform covers of groups, J. Algebra 273 (2004) 153-175, https://doi.org/10.1016/S0021-8693(03)00526-X, Theorem 3.1, eq. (3.1) (subnormal branch only); p. 158–159

import Mathlib

open Pointwise

namespace SubnormalCover

theorem card_cosets_biUnion_ge {G : Type*} [Group G] (H : Subgroup G) (hfin : H.index ≠ 0)
    {k : ℕ} (K : Fin k → Subgroup G) (hHK : ∀ i, H ≤ K i)
    (hsn : ∀ i, (K i).IsSubnormal) (a : Fin k → G) :
    ((Finset.range H.index).filter fun n => ∃ i, (K i).index ∣ n).card
      ≤ ((QuotientGroup.mk '' (⋃ i, (a i) • (K i : Set G)) : Set (G ⧸ H))).ncard := by
  sorry

end SubnormalCover
