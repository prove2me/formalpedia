-- Prove2me | Theorems.Thm_Rep_finrank_invariants_res_coind_eq_finsum
-- name    : Rep.finrank_invariants_res_coind_eq_finsum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/29c09367-15f0-5195-9b48-1a449b1685fe
-- title:
--   Mackey decomposition for invariants of a coinduced representation
-- statement:
--   Let $k$ be a field, $G$ a group, and $H, D \le G$ subgroups with $H$ of finite index in $G$. Let $N$ be a representation of $H$ on a $k$-vector space (in universe $0$) that is finite-dimensional over $k$. Form the coinduced representation $\mathrm{coind}_H^G N$ of $G$ along the inclusion $H \hookrightarrow G$, whose underlying space consists of the maps $f : G \to N$ with $f(hx) = \rho_N(h) f(x)$ for $h \in H$, and restrict it along the inclusion $D \hookrightarrow G$. The assertion is that the $k$-dimension of the space of $D$-invariants of this restriction equals the finite sum, over the quotient of the $H$-set $G/D$ by the orbit relation, of the $k$-dimensions of the spaces of invariants of $N$ restricted to the stabiliser $\mathrm{Stab}_H(q_{\mathrm{out}})$ in $H$ of the chosen representative $q_{\mathrm{out}} \in G/D$ of the orbit class $q$. The right-hand side is a `finsum` over the orbit type, which is finite by the finite-index hypothesis.
--
--   This is the degree-zero Mackey decomposition for a coinduced representation: the $D$-invariants of $\mathrm{coind}_H^G N$ are the $H$-equivariant $N$-valued functions on the $H$-set $G/D$, so their dimension is the sum over $H$-orbits of the dimensions of $N^{\mathrm{Stab}}$. It is used in the archimedean bookkeeping of a local Euler-characteristic computation, being cited by [`groupCohomology.finrank_invariants_archimedean_coind`](thm.html#groupCohomology.finrank_invariants_archimedean_coind).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Rep_finrank_invariants_res_coind_eq_finsum.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory MonoidalCategory Module
open scoped Classical TensorProduct

theorem Rep.finrank_invariants_res_coind_eq_finsum
    {k : Type} [Field k] {G : Type} [Group G] (H D : Subgroup G) [H.FiniteIndex]
    (N : Rep.{0} k H) [FiniteDimensional k N] :
    Module.finrank k (Rep.res D.subtype (Rep.coind H.subtype N)).ρ.invariants =
      ∑ᶠ q : Quotient (MulAction.orbitRel H (G ⧸ D)),
        Module.finrank k (Rep.res (MulAction.stabilizer H q.out).subtype N).ρ.invariants := by sorry
