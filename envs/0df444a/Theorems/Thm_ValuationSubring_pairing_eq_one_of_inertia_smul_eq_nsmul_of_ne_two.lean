-- Prove2me | Theorems.Thm_ValuationSubring_pairing_eq_one_of_inertia_smul_eq_nsmul_of_ne_two
-- name    : ValuationSubring.pairing_eq_one_of_inertia_smul_eq_nsmul_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:03.37934+00:00
-- url     : https://prove2.me/theorems/7aaddff5-7db0-5566-81f4-03c68a6ac924
-- title:
--   Isotropy of a μ-type subset for an inertia-equivariant q^k-th-root pairing, q odd
-- statement:
--   Let $M$ be an additive abelian group carrying a distributive multiplicative action of $G=\operatorname{Gal}(\overline{\mathbf Q}/\mathbf Q)$, where $\overline{\mathbf Q}$ is the algebraic closure `AlgebraicClosure ℚ`. Let $q$ be a prime with $q \neq 2$, and let $A$ be a valuation subring of $\overline{\mathbf Q}$ satisfying `A.LiesOverPrime q`, i.e. the image of $q$ in $\overline{\mathbf Q}$ lies in the nonunits of $A$; write $I_A$ for `A.inertiaSubgroupIn ℚ`, the image of the inertia subgroup of $A$ over $\mathbf Q$ under the inclusion of the decomposition subgroup into $G$. Let $k \in \mathbf N$ and let $n \colon G \to \mathbf N$ satisfy $\sigma(\zeta) = \zeta^{n(\sigma)}$ for every $\sigma \in G$ and every $\zeta \in \overline{\mathbf Q}$ with $\zeta^{q^k} = 1$. Let $B \colon M \times M \to \overline{\mathbf Q}$ be a function and $W \subseteq M$ a subset such that: every $\sigma \in I_A$ acts on each $x \in W$ by $\sigma \cdot x = n(\sigma)\,x$; $W$ is closed under multiples $m \cdot x$ for $m \in \mathbf N$; $B(x,y)^{q^k} = 1$ for $x, y \in W$; $B(m\cdot x, y) = B(x,y)^m = B(x, m \cdot y)$ for $x,y \in W$ and $m \in \mathbf N$; and $B(\sigma \cdot x, \sigma \cdot y) = \sigma(B(x,y))$ for $\sigma \in I_A$ and $x, y \in W$. Then $B(x,y) = 1$ for all $x, y \in W$.
--
--   This is a Galois-descent form of the isotropy step for the multiplicative-type part of Eisenstein torsion: a subset on which inertia at a place above $q$ acts through the cyclotomic character pairs trivially with itself under a pairing valued in $q^k$-th roots of unity, provided $q$ is odd. It is used in the comparison of the Hecke lattice quotient with the image of the reduction of Hecke torsion, via [`ModularCurve.natCard_heckeLatticeAlgebra_quotient_le_natCard_image_reductionModL_heckeTorsion_span_sup`](thm.html#ModularCurve.natCard_heckeLatticeAlgebra_quotient_le_natCard_image_reductionModL_heckeTorsion_span_sup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ValuationSubring_pairing_eq_one_of_inertia_smul_eq_nsmul_of_ne_two.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ValuationSubring.pairing_eq_one_of_inertia_smul_eq_nsmul_of_ne_two
    {M : Type*} [AddCommGroup M] [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) M]
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q)
    (k : ℕ) (n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ)
    (hn : ∀ σ, ∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ k) = 1 → σ ζ = ζ ^ n σ)
    (B : M → M → AlgebraicClosure ℚ)
    (W : Set M)
    (hWμ : ∀ x ∈ W, ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = n σ • x)
    (hWnsmul : ∀ x ∈ W, ∀ m : ℕ, m • x ∈ W)
    (hBval : ∀ x ∈ W, ∀ y ∈ W, B x y ^ (q ^ k) = 1)
    (hBl : ∀ x ∈ W, ∀ y ∈ W, ∀ m : ℕ, B (m • x) y = B x y ^ m)
    (hBr : ∀ x ∈ W, ∀ y ∈ W, ∀ m : ℕ, B x (m • y) = B x y ^ m)
    (hBgal : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x ∈ W, ∀ y ∈ W, B (σ • x) (σ • y) = σ (B x y)) :
    ∀ x ∈ W, ∀ y ∈ W, B x y = 1 := by sorry
