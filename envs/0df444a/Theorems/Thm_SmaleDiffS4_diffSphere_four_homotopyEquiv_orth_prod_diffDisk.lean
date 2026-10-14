-- Prove2me | Theorems.Thm_SmaleDiffS4_diffSphere_four_homotopyEquiv_orth_prod_diffDisk
-- name    : SmaleDiffS4.diffSphere_four_homotopyEquiv_orth_prod_diffDisk
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T12:33:41.772812+00:00
-- url     : https://prove2.me/theorems/f6499526-32b9-4f3c-a9d7-16f68a2dbe44
-- title:
--   $\mathrm{Diff}(S^4)\simeq O(5)\times\mathrm{Diff}(D^4)$
-- statement:
--   Let $\mathrm{Diff}(S^4)$ be the group of all smooth diffeomorphisms of the round unit sphere $S^4\subset\mathbb R^5$, let $O(5)$ be the orthogonal group, and let $\mathrm{Diff}(D^4)$ be the group of diffeomorphisms of the $4$-ball that are the identity on the boundary; the diffeomorphism groups carry the $C^\infty$ topology. Then there is a homotopy equivalence
--
--   $$
--   \mathrm{Diff}(S^4)\;\simeq\; O(5)\times \mathrm{Diff}(D^4).$$
--
--   This reduces every question about the homotopy type of $\mathrm{Diff}(S^4)$ to the same question about $\mathrm{Diff}(D^4)$, which is why the problem is posed for the ball.
--
--   **Formalization Note** The statement asserts the existence of a homotopy equivalence (`ContinuousMap.HomotopyEquiv`) between the two topological spaces; `OrthGroup 5` is $O(5)$ as a subspace of the $5\times5$ real matrices.
-- source:
--   Open Problem Garden, 'What is the homotopy type of the group of diffeomorphisms of the 4-sphere?' (S. Smale; posted by rybu, 2009), http://www.openproblemgarden.org/op/what_is_the_homotopy_type_of_the_group_of_diffeomorphisms_of_the_4_sphere — Problem statement: 'Diff(S^4) has the homotopy-type of a product space Diff(S^4) ≃ O_5 × Diff(D^4)'.

import Mathlib
import Definitions.Def_SmaleDiffS4_Basic

open SmaleDiffS4

namespace SmaleDiffS4

theorem diffSphere_four_homotopyEquiv_orth_prod_diffDisk :
    Nonempty (ContinuousMap.HomotopyEquiv (DiffSphere 4) (OrthGroup 5 × DiffDisk 4)) := by sorry

end SmaleDiffS4
