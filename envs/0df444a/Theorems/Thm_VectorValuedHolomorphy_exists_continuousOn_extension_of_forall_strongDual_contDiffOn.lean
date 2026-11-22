-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_exists_continuousOn_extension_of_forall_strongDual_contDiffOn
-- name    : VectorValuedHolomorphy.exists_continuousOn_extension_of_forall_strongDual_contDiffOn
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:23:43.603505+00:00
-- url     : https://prove2.me/theorems/fccf8599-485a-4b69-88d4-980ff303b4b9
-- title:
--   Lemma C.5.1.22 — removable singularities in dimension one for weakly $C^1$ functions with values in a quasi-complete locally convex space
-- statement:
--   **Removable singularities in dimension one for weakly $C^1$ functions (Lemma C.5.1.22).** Let $k$ be $\mathbb R$ or $\mathbb C$, let $E$ be a quasi-complete Hausdorff locally convex space over $k$, let $\Omega\subset k$ be open, $\xi_0\in\Omega$, and let $f\colon\Omega\setminus\{\xi_0\}\to E$ be a function. Assume that for every continuous linear form $\varphi\in E'$ the scalar function
--   $$\varphi\circ f\colon\Omega\setminus\{\xi_0\}\to k$$
--   is continuously differentiable and extends to a continuously differentiable function on $\Omega$ (differentiability in the sense of the field $k$: real differentiability if $k=\mathbb R$, complex differentiability if $k=\mathbb C$). Then:
--
--   1. there is a continuous function $F\colon\Omega\to E$ extending $f$, and it is unique;
--   2. $F$ is weakly continuously differentiable on $\Omega$: for every $\varphi\in E'$ the function $\varphi\circ F$ is continuously differentiable on $\Omega$.
--
--   The point is that the value $F(\xi_0)$ exists in $E$ and not only in the weak completion: the difference quotients of $f$ near $\xi_0$ form a weakly bounded, hence bounded, set, so $f$ is Lipschitz near $\xi_0$ in the sense of locally convex spaces, and quasi-completeness gives the limit. In the paper the lemma is the key step in the proof of Grothendieck's criterion that a weakly smooth function with values in a quasi-complete space is smooth.
--
--   **Formalization Note.** `f : 𝕜 → E` is a total function whose value at `ξ₀` is irrelevant. The hypothesis is `∀ ℓ : StrongDual 𝕜 E, ∃ g : 𝕜 → 𝕜, ContDiffOn 𝕜 1 g Ω ∧ Set.EqOn g (fun ξ => ℓ (f ξ)) (Ω \ {ξ₀})` (it implies that `ℓ ∘ f` is $C^1$ on the open set `Ω \ {ξ₀}`). The conclusion gives `F : 𝕜 → E` with `ContinuousOn F Ω`, `Set.EqOn F f (Ω \ {ξ₀})`, `ContDiffOn 𝕜 1 (ℓ ∘ F) Ω` for all `ℓ`, and uniqueness on `Ω` among functions continuous on `Ω` that agree with `f` on `Ω \ {ξ₀}`. For `E`, "quasi-complete Hausdorff locally convex space" is `[UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E] [PolynormableSpace 𝕜 E] [T2Space E] [QuasiCompleteSpace 𝕜 E]` (the topology is defined by a family of seminorms; closed von Neumann bounded sets are complete). **Deviation from the source.** In the source $E$ is always a complex space, also when $k=\mathbb R$; here $E$ is a locally convex space over the field `𝕜` of the variable (`[RCLike 𝕜]`). For $k=\mathbb C$ this is the source's statement; for $k=\mathbb R$ the source's case of a complex space $E$ follows by regarding $E$ as a real locally convex space (its real continuous linear forms are the real parts of the complex ones).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 732-733, Lemma C.5.1.22; classical reference: the paper adapts an argument from P. Garrett, Modern Analysis of Automorphic Forms by Example, Vol. 2, Cambridge University Press, 2018, §15.1

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace VectorValuedHolomorphy

/-- Removable singularities in dimension one for weakly `C¹` functions with values in a
quasi-complete Hausdorff locally convex space: if every scalar function `ℓ ∘ f` extends from
`Ω \ {ξ₀}` to a `C¹` function on `Ω`, then `f` extends uniquely to a continuous function on `Ω`,
and the extension is weakly `C¹`. -/
theorem exists_continuousOn_extension_of_forall_strongDual_contDiffOn {𝕜 E : Type*} [RCLike 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [PolynormableSpace 𝕜 E] [T2Space E] [QuasiCompleteSpace 𝕜 E] {Ω : Set 𝕜} (hΩ : IsOpen Ω)
    {ξ₀ : 𝕜} (hξ₀ : ξ₀ ∈ Ω) {f : 𝕜 → E}
    (hf : ∀ ℓ : StrongDual 𝕜 E, ∃ g : 𝕜 → 𝕜, ContDiffOn 𝕜 1 g Ω ∧
      Set.EqOn g (fun ξ => ℓ (f ξ)) (Ω \ {ξ₀})) :
    ∃ F : 𝕜 → E, ContinuousOn F Ω ∧ Set.EqOn F f (Ω \ {ξ₀}) ∧
      (∀ ℓ : StrongDual 𝕜 E, ContDiffOn 𝕜 1 (fun ξ => ℓ (F ξ)) Ω) ∧
      ∀ F' : 𝕜 → E, ContinuousOn F' Ω → Set.EqOn F' f (Ω \ {ξ₀}) → Set.EqOn F' F Ω := by
  sorry

end VectorValuedHolomorphy
