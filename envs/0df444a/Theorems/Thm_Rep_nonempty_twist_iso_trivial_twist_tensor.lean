-- Prove2me | Theorems.Thm_Rep_nonempty_twist_iso_trivial_twist_tensor
-- name    : Rep.nonempty_twist_iso_trivial_twist_tensor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/2e878f36-9701-5aab-acfe-db47e6ec3776
-- title:
--   Twisting a representation is tensoring with a twisted trivial line
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, let $N$ be a $k$-linear representation of $G$ whose underlying module lives in the lowest universe, and let $\chi : G \to k^{\times}$ be a group homomorphism into the units of $k$. For a representation $\rho$ the twist by $\chi$ is the representation on the same underlying module given by $g \mapsto (\chi g) \cdot \rho g$, the scalar $\chi g \in k^{\times}$ acting on the $k$-module; applied to an object of `Rep k G` this produces the object `Rep.of` of that twisted action. The assertion is that the type of isomorphisms in the category `Rep k G` between `N.twist χ` and the monoidal product `(Rep.trivial k G k).twist χ ⊗ N` is nonempty, i.e. that $N(\chi)$ and $k(\chi) \otimes_k N$ are isomorphic as representations, where $k(\chi)$ is the free rank-one module $k$ with $G$ acting through $g \mapsto \chi g$ (the twist of the trivial representation on $k$). Only the mere existence of such an isomorphism is asserted; no specific isomorphism is named in the conclusion.
--
--   This is the standard identification of a $\chi$-twist with the tensor product by the rank-one representation $k(\chi)$, which converts statements about twisted modules into statements about tensor products, e.g. $H^0(G, N(\chi)) = (k(\chi) \otimes N)^{G}$. It is used in the computation of the dimension of the twisted first cohomology group in [`groupCohomology.finiteDimensional_and_finrank_continuousH1Sr_twist_cycloChar_eq_of_trivial`](thm.html#groupCohomology.finiteDimensional_and_finrank_continuousH1Sr_twist_cycloChar_eq_of_trivial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_nonempty_twist_iso_trivial_twist_tensor.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory MonoidalCategory Module groupCohomology ExtCitation
open scoped Classical

theorem Rep.nonempty_twist_iso_trivial_twist_tensor
    {k : Type} [CommRing k] {G : Type} [Group G] (N : Rep.{0} k G) (χ : G →* kˣ) :
    Nonempty (N.twist χ ≅ (Rep.trivial k G k).twist χ ⊗ N) := by sorry
