-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_strongDual_iterate_deriv_eq_circleIntegral
-- name    : VectorValuedHolomorphy.strongDual_iterate_deriv_eq_circleIntegral
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:15.296815+00:00
-- url     : https://prove2.me/theorems/54fe8024-8ebf-452d-b98d-ba0711eaae8b
-- title:
--   Cauchy integral formula for the derivatives of a holomorphic function with values in a quasi-complete locally convex space (on circles)
-- statement:
--   **Cauchy's integral formula for vector-valued holomorphic functions and their derivatives.**
--
--   Let $E$ be a quasi-complete Hausdorff locally convex topological vector space over $\mathbb C$ with continuous dual $E'$, let $U\subset\mathbb C$ be open and let $f:U\to E$ be weakly holomorphic (equivalently, by Grothendieck's theorem, holomorphic), so that all complex derivatives $f^{(k)}:U\to E$ exist. Let $\overline D(c,R)\subset U$ be a closed disc and let $w$ be a point of the open disc $D(c,R)$.
--
--   Then for every integer $k\ge 0$
--   $$f^{(k)}(w)=\frac{k!}{2\pi i}\oint_{|z-c|=R}\frac{f(z)}{(z-w)^{k+1}}\,dz ,$$
--   the integral over the positively oriented circle being understood weakly (in the sense of Pettis): for every $\varphi\in E'$
--   $$\bigl\langle f^{(k)}(w),\varphi\bigr\rangle=\frac{k!}{2\pi i}\oint_{|z-c|=R}\frac{\langle f(z),\varphi\rangle}{(z-w)^{k+1}}\,dz .$$
--   For $k=0$ this is the Cauchy integral formula $f(w)=\frac1{2\pi i}\oint f(z)(z-w)^{-1}dz$.
--
--   The point of the statement is that the left-hand side is a vector of $E$ (the $k$-th derivative of $f$ in $E$), so that the weak integral on the right, a priori only a linear form on $E'$, is represented by an element of $E$. The paper states the formula as an identity in the algebraic dual $(E')^{*}$ "(the left side belongs to $E$)", and uses it for Taylor and Laurent coefficients and for residues.
--
--   **Formalization Note.** `E` is a complex vector space with a uniform structure making it a uniform additive group (`[UniformSpace E] [IsUniformAddGroup E]`), with continuous scalar multiplication, locally convex in the sense of Mathlib's `PolynormableSpace ℂ E` (the topology is defined by a family of seminorms), Hausdorff (`T2Space`) and quasi-complete (`QuasiCompleteSpace ℂ E`: closed von Neumann bounded sets are complete). The continuous dual $E'$ is `StrongDual ℂ E`. The $k$-th derivative is `deriv^[k] f` (iterate of Mathlib's `deriv`, defined for topological vector space targets); the scalar contour integral is Mathlib's `circleIntegral`, written `∮ z in C(c, R), _`. The hypothesis is weak holomorphy on `U`; the identity is stated for each `ℓ : StrongDual ℂ E`, which is exactly the meaning of an identity in $(E')^{*}$ and avoids choosing a vector-valued integral. **Deviation from the source.** The paper allows any closed positively oriented simple curve $\Gamma\subset\Omega$ whose interior is contained in $\Omega$ and any point enclosed by it; Mathlib has no such contours, so the formula is stated for circles (with $w$ anywhere in the open disc). The open set is arbitrary (the source takes a domain).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 738, Theorem C.5.2.6(3), formula (C.5.2.4), and Theorem C.5.2.4(3), formula (C.5.2.3); classical reference: A. Grothendieck, Sur certains espaces de fonctions holomorphes. I, J. reine angew. Math. 192 (1953), pp. 35-64, Theorem 1

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace VectorValuedHolomorphy

theorem strongDual_iterate_deriv_eq_circleIntegral {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] {U : Set ℂ} (hU : IsOpen U) {f : ℂ → E}
    (hf : ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z => ℓ (f z)) U)
    {c : ℂ} {R : ℝ} (hcR : closedBall c R ⊆ U) {w : ℂ} (hw : w ∈ ball c R) (k : ℕ)
    (ℓ : StrongDual ℂ E) :
    ℓ (deriv^[k] f w) =
      ((k.factorial : ℂ) / (2 * π * Complex.I)) *
        ∮ z in C(c, R), ℓ (f z) / (z - w) ^ (k + 1) := by sorry

end VectorValuedHolomorphy
