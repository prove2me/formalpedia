-- Prove2me | Theorems.Thm_Rep_nonempty_tateH0_linearEquiv_homology_normHomCompSub
-- name    : Rep.nonempty_tateH0_linearEquiv_homology_normHomCompSub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/09be4303-defc-5176-ad42-03a7878bfa3c
-- title:
--   Tate ̂ H⁰ as homology of the norm–(g-1) complex
-- statement:
--   Let $k$ be a commutative ring, let $G$ be a commutative group that is finite, let $A$ be a $k$-linear representation of $G$, and let $g \in G$ be an element such that every $x \in G$ lies in the subgroup of integer powers of $g$, i.e. $g$ generates $G$. The assertion is that the type of $k$-linear equivalences between two $k$-modules is nonempty, so that the two are isomorphic, without a named isomorphism being produced. The first module is `A.tateH0`, the degree-zero Tate cohomology of the project: the quotient of the invariants $A^G$ of the representation $\rho$ of $A$ by the range of the map `normBar`, the $k$-linear map from the coinvariants $A_G$ to $A^G$ obtained by descending the norm $a \mapsto \sum_{h \in G} \rho(h)a$, viewed as a map into the invariants, along the quotient $A \to A_G$. The second is the homology of the short complex `FiniteCyclicGroup.normHomCompSub A g`, whose second map is $a \mapsto \rho(g)a - a$, i.e. the quotient of $\ker(\rho(g)-1)$ by the image of the norm.
--
--   This is the degree-zero case of the two-periodicity of the cohomology of a finite cyclic group, identifying $\hat H^0(G,A) = A^G/N_G A$ with the homology of the complex $A \xrightarrow{N} A \xrightarrow{g-1} A$. It feeds the comparison [`Rep.nonempty_tateCohomology_iso_add_two`](thm.html#Rep.nonempty_tateCohomology_iso_add_two), which transports the periodicity isomorphisms $H^{2i}(G,A)$ of the cyclic case to Tate cohomology.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_nonempty_tateH0_linearEquiv_homology_normHomCompSub.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.nonempty_tateH0_linearEquiv_homology_normHomCompSub
    {k G : Type u} [CommRing k] [CommGroup G] [Fintype G] (A : Rep k G) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nonempty (A.tateH0 ≃ₗ[k] (FiniteCyclicGroup.normHomCompSub A g).homology) := by sorry
