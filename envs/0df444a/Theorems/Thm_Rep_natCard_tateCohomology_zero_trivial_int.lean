-- Prove2me | Theorems.Thm_Rep_natCard_tateCohomology_zero_trivial_int
-- name    : Rep.natCard_tateCohomology_zero_trivial_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/04284ff0-e334-5e7c-9b75-2bf81a2c1c87
-- title:
--   The Tate group ̂ H⁰(G,ℤ) has order |G|
-- statement:
--   Let $G$ be a finite group, i.e. a type $G$ carrying a group structure together with a `Fintype` instance, and let `Rep.trivial ℤ G ℤ` be the representation of $G$ on the $\mathbb{Z}$-module $\mathbb{Z}$ on which every group element acts as the identity. For a representation $A$ the project's Tate cohomology `tateCohomology A : ℤ → ModuleCat ℤ` is defined by cases: in degrees $n+1>0$ it is group cohomology, in degrees $-(n+1)<-1$ group homology, in degree $-1$ the kernel of the induced norm map `normBar`, and in degree $0$ the module `tateH0 A`, namely the quotient of the submodule of $G$-invariants of $A$ by the range of `normBar`. The theorem asserts that for this trivial representation the underlying type of `(Rep.trivial ℤ G ℤ).tateCohomology 0`, i.e. of $\mathbb{Z}^G$ modulo the image of the norm, has cardinality (`Nat.card`) equal to `Fintype.card G`, the number of elements of $G$.
--
--   This is the standard computation $\hat H^0(G,\mathbb{Z}) = \mathbb{Z}/|G|\mathbb{Z}$ of Tate cohomology in degree $0$ with trivial integral coefficients. It serves as the source of the order $|G|$ in the duality and counting arguments surrounding Tate's theorem, and is used in the treatment of Tate cup products and of the vanishing of Tate cohomology of splitting modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_natCard_tateCohomology_zero_trivial_int.lean

import Mathlib
import Definitions.Def_GroupCohomology_TateCohomology

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory Rep

theorem Rep.natCard_tateCohomology_zero_trivial_int {G : Type} [Group G] [Fintype G] :
    Nat.card ((Rep.trivial ℤ G ℤ).tateCohomology 0) = Fintype.card G := by sorry
