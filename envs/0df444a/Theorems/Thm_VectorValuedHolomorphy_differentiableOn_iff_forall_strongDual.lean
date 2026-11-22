-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_differentiableOn_iff_forall_strongDual
-- name    : VectorValuedHolomorphy.differentiableOn_iff_forall_strongDual
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:09.430823+00:00
-- url     : https://prove2.me/theorems/8258b02d-478a-4bea-9e9e-a9e5c9c741ee
-- title:
--   Grothendieck's holomorphy criterion: a weakly holomorphic function with values in a quasi-complete locally convex space is holomorphic
-- statement:
--   **Grothendieck's theorem: weak holomorphy equals holomorphy in quasi-complete spaces.**
--
--   Let $E$ be a quasi-complete Hausdorff locally convex topological vector space over $\mathbb C$ (every closed bounded subset of $E$ is complete), with continuous dual $E'$. Let $U\subset\mathbb C$ be open and let $f:U\to E$ be a function. Call $f$ *holomorphic* (complex differentiable) on $U$ if for every $z_0\in U$ the limit
--   $$f'(z_0)=\lim_{z\to z_0}(z-z_0)^{-1}\bigl(f(z)-f(z_0)\bigr)$$
--   exists in $E$ for the given topology of $E$, and *weakly holomorphic* on $U$ if for every $\varphi\in E'$ the scalar function $z\mapsto\langle f(z),\varphi\rangle$ is holomorphic on $U$ in the sense of complex analysis.
--
--   The theorem states that the two notions coincide:
--   $$f\ \text{is holomorphic on }U\iff\ \langle f(\cdot),\varphi\rangle\ \text{is holomorphic on }U\ \text{for every }\varphi\in E'.$$
--
--   The implication $\Rightarrow$ is immediate; the content is $\Leftarrow$, which fails without a completeness assumption. This is the basic tool of vector-valued complex analysis (for Banach spaces it goes back to Dunford): holomorphy of a function with values in a space of operators or distributions can be tested against functionals. In the paper it underlies all statements about holomorphic and meromorphic functions with values in strong duals of Schwartz-Bruhat type spaces, which are quasi-complete.
--
--   **Formalization Note.** `E` is a complex vector space with a uniform structure making it a uniform additive group (`[UniformSpace E] [IsUniformAddGroup E]`), with continuous scalar multiplication, locally convex in the sense of Mathlib's `PolynormableSpace ℂ E` (the topology is defined by a family of seminorms), Hausdorff (`T2Space`) and quasi-complete (`QuasiCompleteSpace ℂ E`: closed von Neumann bounded sets are complete). The continuous dual $E'$ is `StrongDual ℂ E`. Holomorphy of an $E$-valued function is Mathlib's `DifferentiableOn ℂ f U` / `deriv`, which at the pinned Mathlib are defined for topological vector space targets and mean convergence of the difference quotients in $E$ (`Asymptotics.isLittleOTVS_iff_tendsto_inv_smul`). Functions are total maps `ℂ → E`; only their values on the open set matter. The source assumes that the open set is a domain (non-empty and connected); since holomorphy is a local property the statement is given for an arbitrary open set `U`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 738, Theorem C.5.2.6 (Grothendieck's holomorphy criterion), condition (1) and the final assertion, with Definition C.5.2.1 (p. 737); classical reference: A. Grothendieck, Sur certains espaces de fonctions holomorphes. I, J. reine angew. Math. 192 (1953), pp. 35-64, Theorem 1

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace VectorValuedHolomorphy

theorem differentiableOn_iff_forall_strongDual {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] {U : Set ℂ} (hU : IsOpen U) (f : ℂ → E) :
    DifferentiableOn ℂ f U ↔
      ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z => ℓ (f z)) U := by sorry

end VectorValuedHolomorphy
