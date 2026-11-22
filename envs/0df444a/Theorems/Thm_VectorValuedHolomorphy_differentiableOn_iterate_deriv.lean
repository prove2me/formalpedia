-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_differentiableOn_iterate_deriv
-- name    : VectorValuedHolomorphy.differentiableOn_iterate_deriv
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:14.801828+00:00
-- url     : https://prove2.me/theorems/d38685bd-a575-4645-8e1e-c5b469830f46
-- title:
--   A weakly holomorphic function into a quasi-complete locally convex space has complex derivatives of all orders in $E$, computed weakly
-- statement:
--   **Weakly holomorphic functions are infinitely complex differentiable (Grothendieck).**
--
--   Let $E$ be a quasi-complete Hausdorff locally convex topological vector space over $\mathbb C$ with continuous dual $E'$, let $U\subset\mathbb C$ be open and let $f:U\to E$ be weakly holomorphic: $z\mapsto\langle f(z),\varphi\rangle$ is holomorphic on $U$ for every $\varphi\in E'$.
--
--   Then $f$ is complex differentiable any number of times on $U$, with derivatives in $E$: for every integer $k\ge 0$ the $k$-th complex derivative $f^{(k)}:U\to E$ exists (as a limit of difference quotients in the topology of $E$) and is again complex differentiable on $U$. Moreover the derivatives are the weak derivatives:
--   $$\bigl\langle f^{(k)}(z),\varphi\bigr\rangle=\frac{d^{k}}{dz^{k}}\,\langle f(z),\varphi\rangle\qquad(z\in U,\ \varphi\in E',\ k\ge 0).$$
--
--   A priori the right-hand side only defines $f^{(k)}(z)$ as a linear form on $E'$, i.e. as an element of the algebraic dual $(E')^{*}$; the theorem says that this element belongs to $E$ and is the derivative of $f^{(k-1)}$ in $E$. This is the implication (1) $\Rightarrow$ (3) of the paper's Theorem C.5.2.6 together with its formula (C.5.2.6).
--
--   **Formalization Note.** `E` is a complex vector space with a uniform structure making it a uniform additive group (`[UniformSpace E] [IsUniformAddGroup E]`), with continuous scalar multiplication, locally convex in the sense of Mathlib's `PolynormableSpace ℂ E` (the topology is defined by a family of seminorms), Hausdorff (`T2Space`) and quasi-complete (`QuasiCompleteSpace ℂ E`: closed von Neumann bounded sets are complete). The continuous dual $E'$ is `StrongDual ℂ E`. Holomorphy of an $E$-valued function is Mathlib's `DifferentiableOn ℂ f U` / `deriv`, which at the pinned Mathlib are defined for topological vector space targets and mean convergence of the difference quotients in $E$ (`Asymptotics.isLittleOTVS_iff_tendsto_inv_smul`). Functions are total maps `ℂ → E`; only their values on the open set matter. The $k$-th derivative of $f$ is `deriv^[k] f` (the $k$-fold iterate of Mathlib's `deriv`, available for topological vector space targets); for the scalar functions it is Mathlib's `iteratedDeriv k`, which equals `deriv^[k]`. The conclusion is the conjunction of `DifferentiableOn ℂ (deriv^[k] f) U` and the weak-derivative identity on `U`. The open set is arbitrary (the source takes a domain).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 738-739, Theorem C.5.2.6, implication (1) => (3), and formula (C.5.2.6) of Remark C.5.2.7; classical reference: A. Grothendieck, Sur certains espaces de fonctions holomorphes. I, J. reine angew. Math. 192 (1953), pp. 35-64, Theorem 1

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace VectorValuedHolomorphy

theorem differentiableOn_iterate_deriv {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] {U : Set ℂ} (hU : IsOpen U) {f : ℂ → E}
    (hf : ∀ ℓ : StrongDual ℂ E, DifferentiableOn ℂ (fun z => ℓ (f z)) U) (k : ℕ) :
    DifferentiableOn ℂ (deriv^[k] f) U ∧
      ∀ ℓ : StrongDual ℂ E, ∀ z ∈ U,
        ℓ (deriv^[k] f z) = iteratedDeriv k (fun w => ℓ (f w)) z := by sorry

end VectorValuedHolomorphy
