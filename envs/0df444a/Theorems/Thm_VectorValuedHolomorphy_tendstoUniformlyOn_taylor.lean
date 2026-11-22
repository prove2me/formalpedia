-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_tendstoUniformlyOn_taylor
-- name    : VectorValuedHolomorphy.tendstoUniformlyOn_taylor
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:22.294985+00:00
-- url     : https://prove2.me/theorems/c553f656-0e81-4b82-97ff-c80a25116bdd
-- title:
--   Taylor expansion of a holomorphic function with values in a quasi-complete locally convex space, uniformly on closed discs
-- statement:
--   **Taylor expansion of vector-valued holomorphic functions.**
--
--   Let $E$ be a quasi-complete Hausdorff locally convex topological vector space over $\mathbb C$ with continuous dual $E'$, let $U\subset\mathbb C$ be open and let $f:U\to E$ be weakly holomorphic (equivalently, holomorphic), with complex derivatives $f^{(k)}:U\to E$. Let $c\in U$ and put
--   $$a_k=\frac{1}{k!}\,f^{(k)}(c)\in E\qquad(k\ge 0).$$
--
--   Then for every closed disc $\overline D(c,R)=\{z:\ |z-c|\le R\}$ contained in $U$,
--   $$f(z)=\sum_{k\ge 0}a_k\,(z-c)^k\qquad(z\in\overline D(c,R)),$$
--   the series converging in $E$ uniformly on $\overline D(c,R)$: the partial sums $\sum_{k<n}a_k(z-c)^k$ converge to $f(z)$ uniformly in $z\in\overline D(c,R)$ for the uniform structure of $E$, i.e. for every continuous seminorm $p$ on $E$
--   $$\sup_{|z-c|\le R}\ p\Bigl(f(z)-\sum_{k<n}a_k(z-c)^k\Bigr)\xrightarrow[n\to\infty]{}0 .$$
--
--   This is condition (4) of Grothendieck's holomorphy criterion: holomorphic functions with values in a quasi-complete space are analytic, with the same radius of convergence as in the scalar case. It is the source of the Laurent expansions and residues of vector-valued meromorphic functions used in the paper.
--
--   **Formalization Note.** `E` is a complex vector space with a uniform structure making it a uniform additive group (`[UniformSpace E] [IsUniformAddGroup E]`), with continuous scalar multiplication, locally convex in the sense of Mathlib's `PolynormableSpace ℂ E` (the topology is defined by a family of seminorms), Hausdorff (`T2Space`) and quasi-complete (`QuasiCompleteSpace ℂ E`: closed von Neumann bounded sets are complete). The continuous dual $E'$ is `StrongDual ℂ E`. The coefficients are `(k.factorial : ℂ)⁻¹ • deriv^[k] f c`, written inside the sum as `((z - c) ^ k / k.factorial) • deriv^[k] f c`, where `deriv^[k]` is the iterate of Mathlib's `deriv` (defined for topological vector space targets). Uniform convergence of the partial sums `∑ k ∈ Finset.range n, _` is Mathlib's `TendstoUniformlyOn … atTop (closedBall c R)`. The hypothesis is weak holomorphy on `U`. Only the implication (1) $\Rightarrow$ (4) of the source is stated. For $R<0$ the disc is empty, and for $R=0$ the statement reduces to the trivial identity at $z=c$. The open set is arbitrary (the source takes a domain).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 738, Theorem C.5.2.6(4), formula (C.5.2.5); classical reference: A. Grothendieck, Sur certains espaces de fonctions holomorphes. I, J. reine angew. Math. 192 (1953), pp. 35-64, Theorem 1

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace VectorValuedHolomorphy

theorem tendstoUniformlyOn_taylor {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] {U : Set ℂ} (hU : IsOpen U) {f : ℂ → E}
    (hf : ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z => ℓ (f z)) U)
    {c : ℂ} {R : ℝ} (hcR : closedBall c R ⊆ U) :
    TendstoUniformlyOn
      (fun (n : ℕ) (z : ℂ) =>
        ∑ k ∈ Finset.range n, ((z - c) ^ k / (k.factorial : ℂ)) • deriv^[k] f c)
      f atTop (closedBall c R) := by sorry

end VectorValuedHolomorphy
