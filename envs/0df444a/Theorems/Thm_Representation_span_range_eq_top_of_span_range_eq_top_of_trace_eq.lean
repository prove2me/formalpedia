-- Prove2me | Theorems.Thm_Representation_span_range_eq_top_of_span_range_eq_top_of_trace_eq
-- name    : Representation.span_range_eq_top_of_span_range_eq_top_of_trace_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:01.535489+00:00
-- url     : https://prove2.me/theorems/2bb50c6f-38da-5afb-9332-b0d87b0927bc
-- title:
--   Equal traces and dimension propagate End-spanning
-- statement:
--   Let $k$ be a field and $G$ a monoid, and let $V_1,V_2$ be finite-dimensional $k$-vector spaces (abelian groups with $k$-module structures, each assumed finite-dimensional). Let $\rho_1 \colon G \to \operatorname{End}_k(V_1)$ and $\rho_2 \colon G \to \operatorname{End}_k(V_2)$ be monoid homomorphisms into the multiplicative monoids of $k$-linear endomorphisms, i.e. two $k$-linear representations of $G$. Assume three hypotheses: that the dimensions agree, $\dim_k V_1 = \dim_k V_2$; that the $k$-linear span of the image of $\rho_1$, that is of the set $\{\rho_1(g) : g \in G\} \subseteq \operatorname{End}_k(V_1)$, is the whole of $\operatorname{End}_k(V_1)$; and that the two representations have the same trace character, $\operatorname{tr}(\rho_1(g)) = \operatorname{tr}(\rho_2(g))$ in $k$ for every $g \in G$. The conclusion is that the $k$-linear span of $\{\rho_2(g) : g \in G\}$ is likewise the whole of $\operatorname{End}_k(V_2)$. No hypothesis is imposed on the characteristic of $k$, nor is $V_1$ or $V_2$ assumed non-zero.
--
--   By Burnside's theorem the condition that the span of $\rho(G)$ be all of $\operatorname{End}_k(V)$ is, for $V \neq 0$, absolute irreducibility, so the statement says that a representation of the same dimension and with the same trace character as an absolutely irreducible one is itself absolutely irreducible; it is a form of the Frobenius–Schur linear independence of absolutely irreducible trace characters, valid in all characteristics. In this development it is used to transfer absolute irreducibility along trace identities in the Taylor–Wiles Hecke ring arguments, for instance in establishing unipotence on inertia and the existence of bases diagonalising the inertial action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_span_range_eq_top_of_span_range_eq_top_of_trace_eq.lean

import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Representation.span_range_eq_top_of_span_range_eq_top_of_trace_eq
    {k : Type} [Field k] {G : Type} [Monoid G]
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module k V₁] [FiniteDimensional k V₁]
    [AddCommGroup V₂] [Module k V₂] [FiniteDimensional k V₂]
    (ρ₁ : G →* Module.End k V₁) (ρ₂ : G →* Module.End k V₂)
    (hrank : Module.finrank k V₁ = Module.finrank k V₂)
    (hspan₁ : Submodule.span k (Set.range ⇑ρ₁) = ⊤)
    (htr : ∀ g : G, LinearMap.trace k V₁ (ρ₁ g) = LinearMap.trace k V₂ (ρ₂ g)) :
    Submodule.span k (Set.range ⇑ρ₂) = ⊤ := by sorry
