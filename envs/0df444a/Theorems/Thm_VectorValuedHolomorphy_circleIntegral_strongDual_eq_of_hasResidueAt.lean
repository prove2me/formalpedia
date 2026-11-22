-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_circleIntegral_strongDual_eq_of_hasResidueAt
-- name    : VectorValuedHolomorphy.circleIntegral_strongDual_eq_of_hasResidueAt
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:40.543524+00:00
-- url     : https://prove2.me/theorems/844b4d7d-0886-4952-a393-6c1280e86468
-- title:
--   Residue formula $\operatorname{Res}_{z_0}(f)=\frac{1}{2\pi i}\oint f(z)\,dz$ for vector-valued functions with one singularity inside a circle
-- statement:
--   **The residue as a contour integral.**
--
--   Let $E$ be a Hausdorff locally convex topological vector space over $\mathbb C$ with continuous dual $E'$. Let $U\subset\mathbb C$ be open, $z_0\in U$, and let $f:U\setminus\{z_0\}\to E$ be holomorphic and have residue $r=\operatorname{Res}_{z_0}(f)\in E$ at $z_0$, meaning that near $z_0$
--   $$f(z)=\sum_{j=0}^{m}\frac{a_j}{(z-z_0)^{j+1}}+h(z),\qquad a_0=r,$$
--   with $a_j\in E$ and $h$ holomorphic near $z_0$ (so $f$ is meromorphic at $z_0$). Let $\overline D(c,\rho)\subset U$ be a closed disc whose interior contains $z_0$.
--
--   Then
--   $$\operatorname{Res}_{z_0}(f)=\frac{1}{2\pi i}\oint_{|z-c|=\rho}f(z)\,dz ,$$
--   the integral over the positively oriented circle being understood weakly (in the sense of Pettis): for every $\varphi\in E'$
--   $$\oint_{|z-c|=\rho}\langle f(z),\varphi\rangle\,dz=2\pi i\,\bigl\langle \operatorname{Res}_{z_0}(f),\varphi\bigr\rangle .$$
--
--   Thus the weak contour integral of $f$, a priori a linear form on $E'$, is represented by the vector $2\pi i\operatorname{Res}_{z_0}(f)$ of $E$. This is the one-pole case of the vector-valued Residue Theorem of the paper (Theorem C.5.4.1) and its Lemma C.5.3.3(2).
--
--   **Formalization Note.** `E` is a complex topological vector space, locally convex in the sense of Mathlib's `PolynormableSpace ℂ E`, and Hausdorff; $E'$ is `StrongDual ℂ E`. `HasResidueAt f z₀ r` is the predicate of the definition file `VectorValuedHolomorphy_Meromorphic`; holomorphy off $z_0$ is `DifferentiableOn ℂ f (U \ {z₀})` for a total function `f : ℂ → E`. The scalar integral is Mathlib's `circleIntegral`, `∮ z in C(c, ρ), _`, and the identity is stated for each `ℓ : StrongDual ℂ E`. **Deviation from the source.** The paper allows any closed positively oriented simple curve in $\Omega$ enclosing no pole other than possibly $\xi_0$; Mathlib has no such contours, so the formula is stated for circles, with the additional requirement (implicit in the source) that the closed disc lies in the open set where $f$ is defined. The paper's standing hypothesis of quasi-completeness serves to guarantee that the residue exists in $E$; here the residue is given by hypothesis, so that completeness is not needed.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 740, Lemma C.5.3.3(2), formula (C.5.3.7) (see also Lemma C.5.3.2, formula (C.5.3.3) with k = -1)

import Mathlib
import Definitions.Def_VectorValuedHolomorphy_Meromorphic

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace VectorValuedHolomorphy

theorem circleIntegral_strongDual_eq_of_hasResidueAt {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E] {U : Set ℂ} (hU : IsOpen U) {f : ℂ → E}
    {z₀ c : ℂ} {ρ : ℝ} (hcρ : closedBall c ρ ⊆ U) (hz₀ : z₀ ∈ ball c ρ)
    (hf : DifferentiableOn ℂ f (U \ {z₀})) {r : E} (hr : HasResidueAt f z₀ r)
    (ℓ : StrongDual ℂ E) :
    (∮ z in C(c, ρ), ℓ (f z)) = 2 * π * Complex.I * ℓ r := by sorry

end VectorValuedHolomorphy
