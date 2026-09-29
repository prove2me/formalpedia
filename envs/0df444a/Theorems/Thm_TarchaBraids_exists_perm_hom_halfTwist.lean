-- Prove2me | Theorems.Thm_TarchaBraids_exists_perm_hom_halfTwist
-- name    : TarchaBraids.exists_perm_hom_halfTwist
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T18:40:42.322873+00:00
-- url     : https://prove2.me/theorems/8a46cc46-85e0-44dd-b920-536feea52e05
-- title:
--   The underlying-permutation homomorphism, pinned on half-twists
-- statement:
--   There is a homomorphism from the geometric braid group to the symmetric group recording the permutation a braid induces on its endpoints,
--
--   $$
--   u : \pi_1igl(B_{0,n}E^{2}igr) \longrightarrow \mathfrak{S}_n,$$
--
--   which sends each elementary half-twist $[\mathrm{ht}_i]$ to the adjacent transposition exchanging strands $i$ and $i+1$, and whose kernel is exactly the image of the pure braid group under the map induced by the projection from ordered to unordered configurations.
--
--   This is the group-theoretic content of the covering $F_{0,n}E^{2} 	o B_{0,n}E^{2}$, Proposizione 1.1 in Birman's numbering: a loop of unordered configurations returns the puncture set to itself but may permute its points, and the permutation depends only on the homotopy class. The kernel condition says a braid is pure exactly when that permutation is trivial, giving the short exact sequence $1 	o P_n 	o B_n 	o \mathfrak{S}_n 	o 1$.
--
--   The statement differs from `BraidsLinksMCG.prop_1_1_covering` in one essential way. That result asserts the existence of such a $
--   u$ with the stated kernel, but says nothing about its values. A homomorphism known only up to its kernel is useless for computing with generators: composing with an automorphism of $\mathfrak{S}_n$ leaves the kernel unchanged while destroying any relation between $
--   u$ and the half-twists. Pinning $
--   u$ on the half-twists is what makes it possible to conclude that the half-twists surject onto $\mathfrak{S}_n$, which is the use this statement is intended for.
--
--   Surjectivity of $
--   u$ is not asserted, because it follows: the adjacent transpositions generate $\mathfrak{S}_n$, and they are all in the image by the generator condition.
-- source:
--   Tarcha, Braid Theory and the Artin Presentation, Teorema 3.11; Birman, Braids, Links and Mapping Class Groups, Chapter 1, Proposition 1.1 and Theorem 1.4.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem exists_perm_hom_halfTwist (n : ℕ) :
    ∃ nu : GeomBraidGroup n →* Equiv.Perm (Fin n),
      (∀ i : Fin (n - 1), nu (halfTwistBraid n i) =
          Equiv.swap (strandIdx i) (strandIdxSucc i)) ∧
        nu.ker = (FundamentalGroup.map (configProj n) (baseOrdered n)).range := by sorry

end TarchaBraids
