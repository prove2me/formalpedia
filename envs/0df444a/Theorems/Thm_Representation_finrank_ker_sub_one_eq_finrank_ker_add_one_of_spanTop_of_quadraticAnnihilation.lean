-- Prove2me | Theorems.Thm_Representation_finrank_ker_sub_one_eq_finrank_ker_add_one_of_spanTop_of_quadraticAnnihilation
-- name    : Representation.finrank_ker_sub_one_eq_finrank_ker_add_one_of_spanTop_of_quadraticAnnihilation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/05a5aa10-d1e4-5ef9-80c6-95fd3a5f8ea3
-- title:
--   Equal eigenspace dimensions of an involution with ψ(c)=-1
-- statement:
--   Let $k$ be a field with $2 \neq 0$ in $k$, let $G$ be a group, and let $\rho : G \to M_2(k)$ be a monoid homomorphism into the multiplicative monoid of $2 \times 2$ matrices whose image spans $M_2(k)$ as a $k$-vector space, i.e. the $k$-span of $\{\rho(g) : g \in G\}$ is all of $M_2(k)$ (Burnside's criterion for absolute irreducibility). Let $W$ be a finite-dimensional $k$-vector space carrying a $k$-linear representation $\sigma_W$ of $G$, and let $\psi : G \to k^{\times}$ be a group homomorphism such that for every $g \in G$ the endomorphism $\sigma_W(g)$ satisfies the quadratic relation $$\sigma_W(g)^2 - \operatorname{tr}(\rho(g))\,\sigma_W(g) + \psi(g)\cdot \mathrm{id}_W = 0$$ in $\operatorname{End}_k(W)$. Let $c \in G$ satisfy $c \cdot c = 1$ and $\psi(c) = -1$. Then the two eigenspaces of the involution $\sigma_W(c)$ have equal dimension: $$\dim_k \ker(\sigma_W(c) - \mathrm{id}_W) = \dim_k \ker(\sigma_W(c) + \mathrm{id}_W).$$
--
--   This is the dimension-balance consequence of the theorem of Boston, Lenstra and Ribet: a finite-dimensional module on which every $g \in G$ satisfies the characteristic polynomial of $\rho(g)$, for $\rho$ absolutely irreducible in the span sense above, is a direct sum of copies of the standard two-dimensional representation attached to $\rho$, on which an involution with determinant $-1$ has both eigenvalues with multiplicity one. The proof invokes [`Representation.exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation`](thm.html#Representation.exists_blrDecomposition_of_spanTop_of_quadraticAnnihilation), which provides such a decomposition (with $\det \rho(g)$ in place of $\psi(g)$), and the result is used in the construction of a corner submodule and eigenspace description of an $H^1$ in the deformation-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_finrank_ker_sub_one_eq_finrank_ker_add_one_of_spanTop_of_quadraticAnnihilation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Representation.finrank_ker_sub_one_eq_finrank_ker_add_one_of_spanTop_of_quadraticAnnihilation
    {k : Type} [Field k] {G : Type} [Group G]
    (ρ : G →* Matrix (Fin 2) (Fin 2) k)
    {W : Type} [AddCommGroup W] [Module k W] [FiniteDimensional k W]
    (σW : Representation k G W)
    (h2 : (2 : k) ≠ 0)
    (hirr : Submodule.span k (Set.range (fun g : G => ρ g)) = ⊤)
    (ψ : G →* kˣ)
    (hann : ∀ g : G,
      σW g ^ 2 - Matrix.trace (ρ g) • σW g + ((ψ g : kˣ) : k) • (1 : W →ₗ[k] W) = 0)
    (c : G) (hc : c * c = 1) (hψc : ψ c = -1) :
    Module.finrank k ↥(LinearMap.ker (σW c - 1)) =
      Module.finrank k ↥(LinearMap.ker (σW c + 1)) := by sorry
