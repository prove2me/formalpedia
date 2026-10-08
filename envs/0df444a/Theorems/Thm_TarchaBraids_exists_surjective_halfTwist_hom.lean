-- Prove2me | Theorems.Thm_TarchaBraids_exists_surjective_halfTwist_hom
-- name    : TarchaBraids.exists_surjective_halfTwist_hom
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T08:08:43.759143+00:00
-- url     : https://prove2.me/theorems/e75457ec-9f85-484b-8171-38a1e15f7e78
-- title:
--   A surjection $B_n \twoheadrightarrow \pi_1(B_{0,n}E^2)$ matching half-twists
-- statement:
--   There is a surjective group homomorphism from the abstract Artin braid group on $n$ strands onto the geometric braid group $\pi_1(B_{0,n}E^{2})$ which carries each Artin generator $\sigma_i$ to the class $[\mathrm{ht}_i]$ of the corresponding elementary half-twist:
--
--   $$f : B_n \twoheadrightarrow \pi_1\bigl(B_{0,n}E^{2}\bigr), \qquad f(\sigma_i)=[\mathrm{ht}_i].$$
--
--   The statement packages the two geometric facts that make the Artin presentation work in the surjective direction. Existence of the homomorphism is the assertion that the half-twists satisfy Artin's defining relations, so that the assignment $\sigma_i \mapsto [\mathrm{ht}_i]$ extends from the free group to the presented group. Surjectivity is the assertion that every braid can be written as a word in the elementary half-twists, which is Teorema 3.11 of the source in its geometric form: given a loop in the unordered configuration space, one isotopes it so that the punctures cross only in adjacent pairs, and each such crossing contributes a half-twist.
--
--   It is stated with both properties on the same $f$ because that is what the application needs: the image of a generating set under a surjection generates the target, so a homomorphism that is surjective *and* sends generators to half-twists is exactly what forces the half-twists to generate. Splitting the two conditions across different homomorphisms would lose that link.
--
--   The statement says nothing about injectivity, which is the separate and harder half of Artin's theorem.
-- source:
--   Tarcha, Braid Theory and the Artin Presentation, Teorema 3.11 (the half-twists generate) together with the extension half of Teorema 3.15; cf. Birman, Braids, Links and Mapping Class Groups, Chapter 1.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem exists_surjective_halfTwist_hom (n : ℕ) :
    ∃ f : ArtinBraidGroup n →* GeomBraidGroup n,
      (∀ i : Fin (n - 1), f (sigma i) = halfTwistBraid n i) ∧
        Function.Surjective f := by sorry

end TarchaBraids
