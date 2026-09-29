-- Prove2me | Theorems.Thm_Representation_exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing
-- name    : Representation.exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:00.865614+00:00
-- url     : https://prove2.me/theorems/aed5806f-9000-5769-82c5-15938027aa26
-- title:
--   Trace determines representations spanning the endomorphism algebra
-- statement:
--   Let $A$ be a commutative local ring, $G$ a monoid, and $V_1, V_2$ finitely generated free $A$-modules. Let $\rho_1 : G \to \operatorname{End}_A(V_1)$ and $\rho_2 : G \to \operatorname{End}_A(V_2)$ be monoid homomorphisms into the multiplicative monoids of the respective endomorphism algebras. Assume: the ranks agree, $\operatorname{finrank}_A V_1 = \operatorname{finrank}_A V_2$; the $A$-submodule of $\operatorname{End}_A(V_1)$ spanned by the set of values $\rho_1(g)$, $g \in G$, is all of $\operatorname{End}_A(V_1)$, and likewise the $A$-span of the values of $\rho_2$ is all of $\operatorname{End}_A(V_2)$; and the traces agree pointwise, $\operatorname{tr}_A(\rho_1(g)) = \operatorname{tr}_A(\rho_2(g))$ for every $g \in G$. The conclusion is that there exists an $A$-linear isomorphism $e : V_1 \xrightarrow{\sim} V_2$ intertwining the two actions, in the sense that $e(\rho_1(g)\,v) = \rho_2(g)\,(e\,v)$ for all $g \in G$ and all $v \in V_1$. Thus the two representations are isomorphic, not merely conjugate after a base change or up to a twist.
--
--   This is the uniqueness half of Carayol's theorem on representations with prescribed traces over a local ring: a representation whose values span the whole endomorphism algebra (the ring-theoretic form of absolute irreducibility) is determined up to isomorphism by its trace function. It is used in the project to compare $\ell$-adic Galois representations with equal traces whose residual representation is absolutely irreducible, and in the level-lowering argument to produce an intertwiner from equality of characteristic polynomials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Representation_exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing.lean

import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Representation.exists_linearEquiv_of_span_range_eq_top_of_trace_eq_of_isLocalRing
    {A : Type} [CommRing A] [IsLocalRing A] {G : Type} [Monoid G]
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module A V₁] [Module.Free A V₁] [Module.Finite A V₁]
    [AddCommGroup V₂] [Module A V₂] [Module.Free A V₂] [Module.Finite A V₂]
    (ρ₁ : G →* Module.End A V₁) (ρ₂ : G →* Module.End A V₂)
    (hrank : Module.finrank A V₁ = Module.finrank A V₂)
    (hspan₁ : Submodule.span A (Set.range ⇑ρ₁) = ⊤)
    (hspan₂ : Submodule.span A (Set.range ⇑ρ₂) = ⊤)
    (htr : ∀ g : G, LinearMap.trace A V₁ (ρ₁ g) = LinearMap.trace A V₂ (ρ₂ g)) :
    ∃ e : V₁ ≃ₗ[A] V₂, ∀ (g : G) (v : V₁), e (ρ₁ g v) = ρ₂ g (e v) := by sorry
