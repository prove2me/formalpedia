-- Prove2me | Theorems.Thm_TarchaBraids_halfTwist_hom_surjective
-- name    : TarchaBraids.halfTwist_hom_surjective
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-21T17:03:02.073848+00:00
-- url     : https://prove2.me/theorems/c8bf1693-ffe7-4f87-ab8c-ed8a8e65d429
-- title:
--   Half-twist homomorphism is surjective
-- statement:
--   Let $f : B_n \to \pi_1(B_{0,n}E^{2})$ be a group homomorphism from the abstract Artin braid group to the geometric braid group which sends each Artin generator $\sigma_i$ to the class $[\mathrm{ht}_i]$ of the corresponding elementary half-twist. Then $f$ is surjective.
--
--   Equivalently: every element of the geometric braid group is a product of elementary half-twists and their inverses. This is Teorema 3.11 of the source, in the form needed for the Artin presentation.
--
--   The content is genuinely topological. Given a loop in the unordered configuration space $B_{0,n}E^{2}$, one must show it is homotopic to a concatenation of elementary half-twists. The standard route is the Fadell–Neuwirth fibration: forgetting the last point gives a fibration of the ordered configuration space $F_{0,n}E^{2}$ over $F_{0,n-1}E^{2}$ with fibre a punctured plane, and the resulting long exact sequence of homotopy groups lets one induct on $n$, expressing an arbitrary braid in terms of generators of the free fibre group together with braids on fewer strands.
--
--   Note that this statement is about surjectivity only. The existence of such an $f$ is not at issue: it follows from the fact that the half-twists satisfy Artin's defining relations, which is already established, so the assignment $\sigma_i \mapsto [\mathrm{ht}_i]$ extends to the presented group. Injectivity is the separate, harder direction and is not claimed here.
--
--   Because the hypothesis pins $f$ only on the generators, and the generators generate $B_n$, the statement is independent of which such $f$ is chosen.
-- source:
--   Tarcha, Braid Theory and the Artin Presentation, Teorema 3.11 (the elementary half-twists generate the geometric braid group); cf. Birman, Braids, Links and Mapping Class Groups, Chapter 1, and the Fadell–Neuwirth fibration of configuration spaces.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem halfTwist_hom_surjective (n : ℕ)
    (f : ArtinBraidGroup n →* GeomBraidGroup n)
    (hf : ∀ i : Fin (n - 1), f (sigma i) = halfTwistBraid n i) :
    Function.Surjective f := by sorry

end TarchaBraids
