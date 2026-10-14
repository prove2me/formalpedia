-- Prove2me | Theorems.Thm_SmaleDiffS4_diffDisk_four_not_contractible
-- name    : SmaleDiffS4.diffDisk_four_not_contractible
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T12:39:50.733235+00:00
-- url     : https://prove2.me/theorems/e525c0fb-6d98-4b70-9bd0-b8126cea72c9
-- title:
--   $\mathrm{Diff}(D^4)$ is not contractible (Watanabe)
-- statement:
--   Let $\mathrm{Diff}(D^4)$ be the group of diffeomorphisms of the $4$-ball that are the identity on the boundary, with the $C^\infty$ topology. Then
--
--   $$
--   \mathrm{Diff}(D^4) \text{ is not contractible.}$$
--
--   Equivalently (via $\mathrm{Diff}(S^4)\simeq O(5)\times\mathrm{Diff}(D^4)$), the inclusion $O(5)\hookrightarrow\mathrm{Diff}(S^4)$ is not a homotopy equivalence: the $4$-dimensional analogue of the Smale conjecture fails. T. Watanabe proved this by producing nontrivial elements of $\pi_*\mathrm{Diff}(D^4)\otimes\mathbb Q$; it answers the source's question "Determine some (any?) homotopy … groups" in the sense that not all of them vanish, but leaves $\pi_0$ open.
--
--   **Formalization Note** `ContractibleSpace X` means $X$ is homotopy equivalent to a one-point space.
-- source:
--   T. Watanabe, Some exotic nontrivial elements of the rational homotopy groups of Diff(S^4), arXiv:1812.02448 (2018), https://arxiv.org/abs/1812.02448 — abstract: 'As a corollary of the main result, the 4-dimensional Smale conjecture is disproved.' Context: Open Problem Garden, 'What is the homotopy type of the group of diffeomorphisms of the 4-sphere?' (S. Smale; posted by rybu, 2009), http://www.openproblemgarden.org/op/what_is_the_homotopy_type_of_the_group_of_diffeomorphisms_of_the_4_sphere — 'It is unknown whether or not it is connected, or if it has any other non-trivial homotopy or homology groups.'

import Mathlib
import Definitions.Def_SmaleDiffS4_Basic

open SmaleDiffS4

namespace SmaleDiffS4

theorem diffDisk_four_not_contractible : ¬ ContractibleSpace (DiffDisk 4) := by sorry

end SmaleDiffS4
