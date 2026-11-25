-- Prove2me | Theorems.Thm_Representation_Coinvariants_trace_map_tensor_eq_sum_hattoriStallings
-- name    : Representation.Coinvariants.trace_map_tensor_eq_sum_hattoriStallings
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T09:55:27.293212+00:00
-- url     : https://prove2.me/theorems/1c841038-a043-5cf4-9eb5-873334169e0e
-- title:
--   Twisted trace formula for Hattori-Stallings traces: the trace of phi (x) psi on the coinvariants P (x)_{R[G]} M of a projective R[G]-module P
-- statement:
--   Let $R$ be a commutative ring and $G$ a finite group, and let $\rho\colon G \to \mathrm{GL}_R(P)$ and $\tau\colon G \to \mathrm{GL}_R(M)$ be representations of $G$ on $R$-modules $P$ and $M$ that are free of finite rank over $R$. Suppose that $P$ is projective over $R[G]$, as witnessed by Higman's criterion: an $R$-linear map $E\colon P \to P$ with
--
--   $$\sum_{h \in G} \rho(h) \circ E \circ \rho(h)^{-1} = \mathrm{id}_P .$$
--
--   For a $G$-equivariant endomorphism $\varphi$ of $P$, its *Hattori-Stallings trace* is the function on the set of conjugacy classes of $G$ given by
--
--   $$\mathrm{hs}(\varphi)(c) = \sum_{g \in c} \operatorname{Tr}_R\bigl(\rho(g)^{-1} \circ \varphi \circ E \mid P\bigr).$$
--
--   Let $\psi$ be a $G$-equivariant endomorphism of $M$. Let $(P \otimes_R M)_G = P \otimes_{R[G]} M$ be the coinvariants of the diagonal action of $G$ on $P \otimes_R M$, assumed free over $R$ (automatic if $R$ is a field or a local ring), and let $(\varphi \otimes \psi)_G$ be the endomorphism of it induced by the equivariant map $\varphi \otimes \psi$. Then:
--
--   1. (*twisted trace formula*) for every choice of representatives $g_c \in c$ of the conjugacy classes,
--
--   $$\operatorname{Tr}_R\bigl((\varphi \otimes \psi)_G \mid (P \otimes_R M)_G\bigr) = \sum_{c} \mathrm{hs}(\varphi)(c)\, \operatorname{Tr}_R\bigl(\tau(g_c)^{-1} \circ \psi \mid M\bigr);$$
--
--   2. for every $\gamma \in G$, with $Z_G(\gamma)$ the centralizer of $\gamma$ and $[\gamma]$ its conjugacy class,
--
--   $$\operatorname{Tr}_R\bigl(\rho(\gamma)^{-1} \circ \varphi \mid P\bigr) = |Z_G(\gamma)| \cdot \mathrm{hs}(\varphi)([\gamma]);$$
--
--   3. $\mathrm{hs}(\varphi)$ does not depend on $E$: every $E'\colon P \to P$ with $\sum_{h} \rho(h) \circ E' \circ \rho(h)^{-1} = \mathrm{id}_P$ gives the same function of $c$.
--
--   This is the linear-algebra core of the twisted trace formula in Deligne's *Rapport sur la formule des traces* (SGA 4½), which computes traces on $P \otimes_{R[G]} M$, the shape taken by the cohomology of a sheaf obtained from a Galois cover with group $G$ by twisting with the representation $M$. Part 1 shows that the trace there depends only on the Hattori-Stallings trace of $\varphi$ and on the twisted character $c \mapsto \operatorname{Tr}(\tau(g_c)^{-1} \circ \psi)$ of $M$ (which is a class function since $\psi$ is equivariant), and part 3 shows that $\mathrm{hs}(\varphi)$ is intrinsic to $\varphi$. When $|G|$ is invertible in $R$ one may take $E = |G|^{-1}\,\mathrm{id}_P$, and part 1 reduces to the familiar character computation of a trace on coinvariants; the point of the formula is that it holds without that assumption, for instance over $\mathbb Z/\ell^n$ with $\ell$ dividing $|G|$. Part 2 relates $\mathrm{hs}(\varphi)$ to the ordinary twisted traces on $P$; since $|Z_G(\gamma)|$ need not be invertible in $R$, $\mathrm{hs}(\varphi)$ carries more information than those traces.
--
--   **Formalization Note**: The representations are Mathlib's `Representation R G P` and `Representation R G M` (the module $P$ with $G$ acting through $\rho$ is the $R[G]$-module), and all types live in `Type`. The Higman datum is the variable `E` with hypothesis `hE`. The equivariant endomorphisms are `φ : ρ.IntertwiningMap ρ` and `ψ : τ.IntertwiningMap τ` with underlying linear maps `φ.toLinearMap` and `ψ.toLinearMap`. The coinvariants of the diagonal action are `Representation.Coinvariants (ρ.tprod τ)`, and $(\varphi \otimes \psi)_G$ is `Representation.Coinvariants.map (ρ.tprod τ) (ρ.tprod τ) (φ.tensor ψ)`. Mathlib's `LinearMap.trace` is defined to be $0$ on a module without a finite basis, so freeness of the coinvariants is assumed as the instance hypothesis `[Module.Free R (Representation.Coinvariants (ρ.tprod τ))]` (finiteness is a Mathlib instance). The Hattori-Stallings trace is the variable `hs : ConjClasses G → R` with defining equation `hhs`; the sum over a conjugacy class $c$ is `∑ g : G with ConjClasses.mk g = c`, and `[DecidableEq G]` makes membership in a class decidable. In part 1 the representatives are any `r : ConjClasses G → G` with `ConjClasses.mk (r c) = c`; in part 2 $|Z_G(\gamma)|$ is `Nat.card (Subgroup.centralizer {γ})` cast to $R$.
-- source:
--   P. Deligne, Rapport sur la formule des traces, in Cohomologie étale (SGA 4½), Lecture Notes in Mathematics 569, Springer (1977); A. Hattori, Rank element of a projective module, Nagoya Math. J. 25 (1965); J. Stallings, Centerless groups - an algebraic formulation of Gottlieb's theorem, Topology 4 (1965)

import Mathlib

set_option autoImplicit false

theorem Representation.Coinvariants.trace_map_tensor_eq_sum_hattoriStallings
    (R G P M : Type) [CommRing R] [Group G] [Fintype G] [DecidableEq G]
    [AddCommGroup P] [Module R P] [Module.Free R P] [Module.Finite R P]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (ρ : Representation R G P) (τ : Representation R G M)
    [Module.Free R (Representation.Coinvariants (ρ.tprod τ))]
    (E : P →ₗ[R] P) (hE : ∑ h : G, ρ h ∘ₗ E ∘ₗ ρ h⁻¹ = LinearMap.id)
    (φ : ρ.IntertwiningMap ρ) (ψ : τ.IntertwiningMap τ)
    (hs : ConjClasses G → R)
    (hhs : ∀ c, hs c = ∑ g : G with ConjClasses.mk g = c,
      LinearMap.trace R P (ρ g⁻¹ ∘ₗ φ.toLinearMap ∘ₗ E)) :
    (∀ r : ConjClasses G → G, (∀ c, ConjClasses.mk (r c) = c) →
      LinearMap.trace R (Representation.Coinvariants (ρ.tprod τ))
          (Representation.Coinvariants.map (ρ.tprod τ) (ρ.tprod τ) (φ.tensor ψ)) =
        ∑ c : ConjClasses G, hs c * LinearMap.trace R M (τ (r c)⁻¹ ∘ₗ ψ.toLinearMap)) ∧
    (∀ γ : G, LinearMap.trace R P (ρ γ⁻¹ ∘ₗ φ.toLinearMap) =
      (Nat.card (Subgroup.centralizer {γ}) : R) * hs (ConjClasses.mk γ)) ∧
    (∀ E' : P →ₗ[R] P, ∑ h : G, ρ h ∘ₗ E' ∘ₗ ρ h⁻¹ = LinearMap.id →
      ∀ c, hs c = ∑ g : G with ConjClasses.mk g = c,
        LinearMap.trace R P (ρ g⁻¹ ∘ₗ φ.toLinearMap ∘ₗ E')) := by
  sorry
