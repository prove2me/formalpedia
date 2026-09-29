-- Prove2me | Theorems.Thm_TarchaBraids_geom_braid_artin_action
-- name    : TarchaBraids.geom_braid_artin_action
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-21T17:14:39.057217+00:00
-- url     : https://prove2.me/theorems/7967306f-d7eb-4599-b54d-b064763f1f7a
-- title:
--   The geometric braid group acts on $F_n$ by Artin's automorphisms
-- statement:
--   The geometric braid group acts on the free group of rank $n$ by Artin's formulas: there is a group homomorphism
--
--   $$ho : \pi_1igl(B_{0,n}E^{2}igr) \longrightarrow \operatorname{Aut}(F_n)$$
--
--   sending the class $[\mathrm{ht}_i]$ of each elementary half-twist to Artin's automorphism $\mathrm{artinEndo}(n,i)$, which maps $x_i \mapsto x_i x_{i+1} x_i^{-1}$, $x_{i+1} \mapsto x_i$, and fixes the remaining generators.
--
--   This is the geometric side of Artin's theory, and it is stated here for the *geometric* braid group rather than the abstract one. The platform already records the abstract counterpart, `BraidsLinksMCG.artin_representation_wellDefined`, which produces a homomorphism out of the presented group $B_n$ with the same generator values; that one is a purely algebraic check that the Artin automorphisms satisfy the braid relations. The present statement is different in kind: the source is $\pi_1$ of the unordered configuration space, so the homomorphism cannot be built by checking relations on generators, and the content is topological.
--
--   The classical construction is via mapping classes. A loop in $B_{0,n}E^{2}$ is realised, by isotopy extension, as an ambient isotopy of the plane fixing the puncture set setwise, whose time-one map is a homeomorphism $h$ of $E^{2}-Q_n$ fixing the base point. Such an $h$ induces an automorphism $h_*$ of $\pi_1(E^{2}-Q_n) \cong F_n$, the assignment $[\gamma] \mapsto h_*$ is well defined on homotopy classes of loops, and it is a homomorphism because composition of mapping classes corresponds to composition of induced maps. Evaluating it on an elementary half-twist gives precisely Artin's formulas: the half-twist $\mathrm{ht}_i$ drags the $i$-th puncture around the $(i+1)$-st, conjugating the $i$-th free generator by itself and exchanging the two.
--
--   Nothing about faithfulness is claimed here. This is the existence and generator-value statement only; injectivity of $ho$, or of the composite with $B_n 	o \pi_1$, is a separate matter.
-- source:
--   Birman, Braids, Links and Mapping Class Groups, Chapter 1, equation (1-14) and the discussion of the action of the braid group on the free group; Tarcha, Braid Theory and the Artin Presentation, the geometric form of the Artin representation.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinEndo
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_TarchaBraids_HalfTwist

namespace TarchaBraids

open BraidsLinksMCG

theorem geom_braid_artin_action (n : ℕ) :
    ∃ rho : GeomBraidGroup n →* MulAut (FreeGroup (Fin n)),
      ∀ i : Fin (n - 1), ∀ w : FreeGroup (Fin n),
        rho (halfTwistBraid n i) w = artinEndo n i w := by sorry

end TarchaBraids
