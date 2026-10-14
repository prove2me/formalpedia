-- Prove2me | Theorems.Thm_SmaleDiffS4_diffDisk_four_pathConnected
-- name    : SmaleDiffS4.diffDisk_four_pathConnected
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-11T12:47:50.106502+00:00
-- url     : https://prove2.me/theorems/5ecceafe-4175-46c1-a6dd-fd27ddd396c5
-- title:
--   $\mathrm{Diff}(D^4 \text{ rel } \partial)$ is path-connected
-- statement:
--   Let $\mathrm{Diff}(D^4)$ denote the group of smooth diffeomorphisms of the closed $4$-ball that restrict to the identity on the boundary sphere, with the $C^\infty$ topology. The open question singled out in the source is whether this group is connected. The goal asserts that it is:
--
--   $$
--   \pi_0\,\mathrm{Diff}(D^4) = 0, \qquad \text{i.e. } \mathrm{Diff}(D^4) \text{ is path-connected.}$$
--
--   Since $\mathrm{Diff}(S^4)\simeq O(5)\times\mathrm{Diff}(D^4)$, this is equivalent to $\pi_0\,\mathrm{Diff}(S^4)\cong\mathbb Z/2$, i.e. every orientation-preserving diffeomorphism of $S^4$ is smoothly isotopic to the identity. The status is open: a proof settles the question positively, a disproof (exhibiting a diffeomorphism not isotopic to the identity rel boundary) settles it negatively.
--
--   **Formalization Note** `DiffDisk 4` is the group of diffeomorphisms of $\mathbb R^4$ equal to the identity at every point of norm $\ge 1$, with the topology of uniform convergence of all derivatives; this is the standard model of $\mathrm{Diff}(D^4\text{ rel }\partial)$. For a topological space, path-connected means nonempty with any two points joined by a path, i.e. $\pi_0$ is a single point.
-- source:
--   Open Problem Garden, 'What is the homotopy type of the group of diffeomorphisms of the 4-sphere?' (S. Smale; posted by rybu, 2009), http://www.openproblemgarden.org/op/what_is_the_homotopy_type_of_the_group_of_diffeomorphisms_of_the_4_sphere — Problem statement: 'It is unknown whether or not it is connected'.

import Mathlib
import Definitions.Def_SmaleDiffS4_Basic

open SmaleDiffS4

namespace SmaleDiffS4

theorem diffDisk_four_pathConnected : PathConnectedSpace (DiffDisk 4) := by sorry

end SmaleDiffS4
