-- Prove2me | Theorems.Thm_ValuationSubring_forall_mem_comap_iff_of_centred_of_isInvariant
-- name    : ValuationSubring.forall_mem_comap_iff_of_centred_of_isInvariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/cd229c70-42a7-5ccd-a44a-1426d6ca3782
-- title:
--   Descent of the centred valuation ring to the fixed subfield
-- statement:
--   Let $F$ be a field carrying a faithful action of a finite group $G$ by ring automorphisms, let $B_1$ be a commutative ring with a $G$-action by ring automorphisms and an algebra structure over a commutative ring $B_2$ whose scalars commute with the $G$-action, and assume $B_2 \to B_1$ is invariant in the sense of `Algebra.IsInvariant`, i.e. every $G$-fixed element of $B_1$ comes from $B_2$. Let $\rho_1 : B_1 \to F$ be a ring homomorphism with $\rho_1(g \cdot b) = g \cdot \rho_1(b)$, suppose every element of $B_1$ is integral over $B_2$, and let $\mathfrak y \subset B_1$ be a prime ideal. Let $P$ be a valuation subring of $F$ with $\rho_1(B_1) \subseteq P$ and $\rho_1(b)$ a non-unit of $P$ exactly when $b \in \mathfrak y$, and assume $P$ is the only valuation subring of $F$ with these two properties. Let $\theta_E$ be a ring homomorphism from the fixed subfield $F^G$ to a field $E'$ and $W$ a valuation subring of $E'$. Assume, for each $b \in B_2$, that $\rho_1$ of the image of $b$ in $B_1$ is $G$-fixed, that its image under $\theta_E$ lies in $W$, and that this image is a non-unit of $W$ exactly when the image of $b$ in $B_1$ lies in $\mathfrak y$. Then for every $e \in F^G$ one has $\theta_E(e) \in W$ if and only if $e \in P$.
--
--   This is a normality-free form of the descent of a uniquely determined centred valuation ring along the passage to the invariants of a finite group action: the valuation subring of the fixed field pulled back from $W$ is forced to be the contraction of $P$. It is used in the computation of the cardinality of an inertia group at a point of a two-chart integral model of the modular curve $X_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_forall_mem_comap_iff_of_centred_of_isInvariant.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Pointwise

theorem ValuationSubring.forall_mem_comap_iff_of_centred_of_isInvariant
    {F : Type*} [Field F] {G : Type*} [Group G] [MulSemiringAction G F] [Fintype G] [FaithfulSMul G F]
    {B₂ B₁ E' : Type*} [CommRing B₂] [CommRing B₁] [Field E'] [Algebra B₂ B₁]
    [MulSemiringAction G B₁] [SMulCommClass G B₂ B₁] [Algebra.IsInvariant B₂ B₁ G]
    (ρ₁ : B₁ →+* F) (hρ₁G : ∀ (g : G) (b : B₁), ρ₁ (g • b) = g • ρ₁ b)
    (hint : ∀ b : B₁, IsIntegral B₂ b)
    (𝔶 : Ideal B₁) [𝔶.IsPrime]
    (P : ValuationSubring F) (hP : ∀ b, ρ₁ b ∈ P) (hPy : ∀ b, ρ₁ b ∈ P.nonunits ↔ b ∈ 𝔶)
    (huniq : ∀ P' : ValuationSubring F, (∀ b, ρ₁ b ∈ P') → (∀ b, ρ₁ b ∈ P'.nonunits ↔ b ∈ 𝔶) → P' = P)
    (θE : ↥(FixedPoints.subfield G F) →+* E') (W : ValuationSubring E')
    (hfix : ∀ (g : G) (b : B₂), g • ρ₁ (algebraMap B₂ B₁ b) = ρ₁ (algebraMap B₂ B₁ b))
    (hint₂ : ∀ b : B₂, θE ⟨ρ₁ (algebraMap B₂ B₁ b), fun g => hfix g b⟩ ∈ W)
    (hcent₂ : ∀ b : B₂, θE ⟨ρ₁ (algebraMap B₂ B₁ b), fun g => hfix g b⟩ ∈ W.nonunits ↔ algebraMap B₂ B₁ b ∈ 𝔶) :
    ∀ e : ↥(FixedPoints.subfield G F), θE e ∈ W ↔ (e : F) ∈ P := by sorry
