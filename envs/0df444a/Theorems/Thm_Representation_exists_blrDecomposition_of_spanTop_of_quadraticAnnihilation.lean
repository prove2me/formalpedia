-- Prove2me | Theorems.Thm_Representation_exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation
-- name    : Representation.exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/d10a3608-1fad-592b-abb5-d6ef13ec58f9
-- title:
--   Boston–Lenstra–Ribet: quadratic annihilation forces W≅ρ^{⊕ n}
-- statement:
--   Let $k$ be a field, $G$ a group, and $\rho\colon G\to M_2(k)$ a monoid homomorphism into the multiplicative monoid of $2\times 2$ matrices over $k$. Let $W$ be a finite-dimensional $k$-vector space carrying a $k$-linear representation $\sigma_W$ of $G$. Assume $2\neq 0$ in $k$; assume the Burnside condition that the $k$-span of the set of matrices $\{\rho(g):g\in G\}$ is all of $M_2(k)$; and assume that for every $g\in G$ the endomorphism $\sigma_W(g)$ is annihilated by the characteristic polynomial of $\rho(g)$, i.e. $\sigma_W(g)^2-\mathrm{tr}(\rho(g))\,\sigma_W(g)+\det(\rho(g))\,\mathrm{id}_W=0$ in $\mathrm{End}_k(W)$. The conclusion is that there exist a natural number $n$ and a $k$-linear isomorphism $e\colon W\xrightarrow{\ \sim\ }(\mathrm{Fin}\,n\to k^2)$, that is onto $n$ copies of the standard column space $k^2$, such that for all $g\in G$, all $w\in W$ and each index $i<n$ one has $e(\sigma_W(g)w)_i=\rho(g)\cdot e(w)_i$, the matrix acting on the $i$-th column by matrix–vector multiplication. Thus $W$ is $G$-isomorphic to the direct sum of $n$ copies of the representation $\rho$; the zero module is covered by $n=0$, and $\dim_k W=2n$ follows.
--
--   This is the theorem of Boston, Lenstra and Ribet: a representation on which every group element satisfies the characteristic polynomial of a fixed absolutely irreducible two-dimensional representation (in the Burnside spelling, the image spanning the full matrix algebra) is a direct sum of copies of that representation. In this development it replaces the duality argument in the level-lowering step, and is applied to Hecke-module torsion in Jacobians of modular curves, as well as to the comparison of kernel dimensions of $\sigma_W(g)\mp 1$ and to constructing injective equivariant maps over Artinian reduced coefficient rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open Matrix

theorem Representation.exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation
    {k : Type} [Field k] {G : Type} [Group G]
    (ρ : G →* Matrix (Fin 2) (Fin 2) k)
    {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σW : Representation k G W)
    (h2 : (2 : k) ≠ 0)
    (hirr : Submodule.span k (Set.range (fun g : G => ρ g)) = ⊤)
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + (ρ g).det • (1 : W →ₗ[k] W) = 0) :
    ∃ (n : ℕ) (e : W ≃ₗ[k] (Fin n → (Fin 2 → k))),
      ∀ (g : G) (w : W) (i : Fin n), e (σW g w) i = (ρ g).mulVec (e w i) := by sorry
