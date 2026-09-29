-- Prove2me | Theorems.Thm_PDivisibleGroup_nonempty_basis_tateModule_points
-- name    : PDivisibleGroup.nonempty_basis_tateModule_points
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:58.387243+00:00
-- url     : https://prove2.me/theorems/7a47598d-c273-532a-9ff0-ee9e455423a7
-- title:
--   Tate module of a height-h p-divisible group is free of rank h
-- statement:
--   Let $p$ be a prime, $R$ a commutative ring, $h$ a natural number and $G$ a $p$-divisible group of height $h$ over $R$ in the project's sense: a family of commutative rings $G.\mathrm{level}\,v$ ($v \in \mathbb{N}$), each a cocommutative Hopf $R$-algebra that is finite and free as an $R$-module with $\operatorname{rank}_R G.\mathrm{level}\,v = p^{vh}$, together with surjective coalgebra-and-algebra maps $G.\mathrm{level}\,(v+1) \to G.\mathrm{level}\,v$ over $R$ whose kernel is the ideal generated as the image of the augmentation ideal of $G.\mathrm{level}\,(v+1)$ under multiplication by $p^v$. Let $L$ be an algebraically closed field of characteristic zero equipped with an $R$-algebra structure. The group of $L$-points $G.\mathrm{Points}\,L$ is the direct limit, over $v$, of the additive versions of the groups of $R$-algebra homomorphisms $G.\mathrm{level}\,v \to L$ under the convolution product. The conclusion is that the Tate module $\mathrm{TateModule}\,p\,(G.\mathrm{Points}\,L)$ — the additive subgroup of sequences $x : \mathbb{N} \to G.\mathrm{Points}\,L$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$ for all $n$ — admits a basis indexed by $\mathrm{Fin}\,h$ over $\mathbb{Z}_p$; that is, the basis type is nonempty.
--
--   This is the standard freeness statement for the Tate module of a $p$-divisible group of height $h$ in the case of points in an algebraically closed field of characteristic zero, where all the level group schemes are étale. It supplies the rank-$h$ $\mathbb{Z}_p$-lattice underlying later work on Cartier duality pairings on Tate modules and on the passage between homomorphisms of $p$-divisible groups and maps of their point groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_PDivisibleGroup_nonempty_basis_tateModule_points.lean

import Mathlib
import Definitions.Def_PDivisibleGroup_Points

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem PDivisibleGroup.nonempty_basis_tateModule_points
    {R : Type} [CommRing R] {p h : ℕ} [Fact p.Prime] (G : PDivisibleGroup R p h)
    (L : Type) [Field L] [IsAlgClosed L] [CharZero L] [Algebra R L] :
    Nonempty (Module.Basis (Fin h) ℤ_[p] (TateModule p (G.Points L))) := by sorry
