-- Prove2me | Theorems.Thm_TarchaBraids_braid_inclusion_hom_injective
-- name    : TarchaBraids.braid_inclusion_hom_injective
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T17:46:02.816455+00:00
-- url     : https://prove2.me/theorems/0b6985cc-01b9-4723-95f3-ff5a8c166ef9
-- title:
--   The natural map $B_m 	o B_n$ is injective
-- statement:
--   Let $m \le n$ and let $f : B_m 	o B_n$ be a group homomorphism carrying each Artin generator $\sigma_i$ of $B_m$ to the generator of $B_n$ with the same index. Then $f$ is injective.
--
--   Equivalently: the braid group on $m$ strands embeds in the braid group on $n$ strands, in the evident way, by adding $n - m$ strands that are never braided. This is the substance of Proposizione 3.17 of the source.
--
--   Only injectivity is asserted. That such an $f$ exists is elementary and needs no assumption: the index map $i \mapsto \mathrm{castLE}(i)$ preserves numerical index values, so each defining relator of $B_m$ --- commutation for $|i-j| \ge 2$ and the braid relation for $j = i+1$ --- maps to the corresponding relator of $B_n$, and the assignment extends to the presented group. The statement is therefore phrased for an arbitrary $f$ pinned on generators, which by the generation of $B_m$ determines $f$ uniquely and makes the statement independent of the choice.
--
--   Injectivity is not formal. It is false for general maps of presented groups that match generators --- adding relations can collapse a group --- so something specific to braids is needed. The classical argument is geometric: a braid on $m$ strands that becomes trivial after adding $n-m$ unbraided strands is already trivial, because the extra strands can be pushed out of the way. A purely algebraic route runs through the Artin representation: the action of $B_n$ on $F_n$ restricts on the subgroup $\langle x_1, \ldots, x_m angle \cong F_m$ to the action of $B_m$ on $F_m$, so faithfulness of the Artin representation of $B_m$ forces $f$ to be injective.
--
--   Note that this is weaker than asking the inclusion to split. A retraction $B_n 	o B_m$ would give injectivity at once, but no retraction is claimed here, and the naive candidate --- killing the generators of index $\ge m-1$ --- does not respect the braid relation linking $\sigma_{m-2}$ and $\sigma_{m-1}$.
-- source:
--   Tarcha, Braid Theory and the Artin Presentation, Proposizione 3.17; cf. Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup

namespace TarchaBraids

open BraidsLinksMCG

theorem braid_inclusion_hom_injective {m n : ℕ} (h : m ≤ n)
    (f : ArtinBraidGroup m →* ArtinBraidGroup n)
    (hf : ∀ i : Fin (m - 1), f (sigma i) = sigma (Fin.castLE (Nat.sub_le_sub_right h 1) i)) :
    Function.Injective f := by sorry

end TarchaBraids
