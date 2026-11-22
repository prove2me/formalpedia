-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_eqOn_of_eqOn_ball
-- name    : VectorValuedHolomorphy.eqOn_of_eqOn_ball
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:19.234959+00:00
-- url     : https://prove2.me/theorems/f8187b3a-d83a-48e2-a14e-fe0aa044923d
-- title:
--   Identity theorem for vector-valued functions holomorphic off discrete sets (in particular meromorphic functions) on a domain
-- statement:
--   **Identity theorem for vector-valued holomorphic and meromorphic functions.**
--
--   Let $E$ be a Hausdorff locally convex topological vector space over $\mathbb C$ and let $\Omega\subset\mathbb C$ be a domain (open and connected). For $i=1,2$ let $D_i\subset\Omega$ be a discrete subset, closed in $\Omega$ (no accumulation point in $\Omega$), and let $f_i:\Omega\setminus D_i\to E$ be holomorphic; for instance $(f_i,D_i)$ may be a meromorphic $E$-valued function on $\Omega$ with pole set $D_i$. Suppose that $f_1$ and $f_2$ coincide on a non-empty open disc $B\subset\Omega\setminus(D_1\cup D_2)$:
--   $$f_1|_B=f_2|_B .$$
--
--   Then they coincide wherever both are defined:
--   $$f_1(z)=f_2(z)\qquad\text{for all }z\in\Omega\setminus(D_1\cup D_2).$$
--
--   For $D_1=D_2=\varnothing$ this is the identity theorem for $E$-valued holomorphic functions on a domain. It expresses the uniqueness of holomorphic and meromorphic continuation of vector-valued functions, which the paper uses repeatedly (for example for distribution-valued zeta integrals first defined on a half-plane).
--
--   **Formalization Note.** `E` is a complex topological vector space, locally convex in the sense of Mathlib's `PolynormableSpace ℂ E`, and Hausdorff. Holomorphy of an $E$-valued function is Mathlib's `DifferentiableOn ℂ f U` / `deriv`, which at the pinned Mathlib are defined for topological vector space targets and mean convergence of the difference quotients in $E$ (`Asymptotics.isLittleOTVS_iff_tendsto_inv_smul`). Functions are total maps `ℂ → E`; only their values on the open set matter. "No accumulation point of $D_i$ in $\Omega$" is `∀ z ∈ Ω, ∀ᶠ w in 𝓝[≠] z, w ∉ Dᵢ`; connectedness is `IsPreconnected Ω` (non-emptiness follows from the disc). **Deviation from the source.** Lemma C.5.4.3 is stated for meromorphic pairs $(f_i,D_i)$ with values in a quasi-complete space. Neither the behaviour of $f_i$ at the points of $D_i$ nor quasi-completeness is needed for the conclusion, so the formal statement assumes only holomorphy off $D_i$ and a Hausdorff locally convex target; it contains the lemma of the source as a special case.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 741, Lemma C.5.4.3 (Vector-valued Identity Theorem, §C.5.4.1)

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace VectorValuedHolomorphy

theorem eqOn_of_eqOn_ball {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E] {Ω D₁ D₂ : Set ℂ} (hΩ : IsOpen Ω) (hΩc : IsPreconnected Ω)
    (hD₁ : ∀ z ∈ Ω, ∀ᶠ w in 𝓝[≠] z, w ∉ D₁) (hD₂ : ∀ z ∈ Ω, ∀ᶠ w in 𝓝[≠] z, w ∉ D₂)
    {f₁ f₂ : ℂ → E} (hf₁ : DifferentiableOn ℂ f₁ (Ω \ D₁))
    (hf₂ : DifferentiableOn ℂ f₂ (Ω \ D₂)) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hB : ball c r ⊆ Ω \ (D₁ ∪ D₂)) (h : Set.EqOn f₁ f₂ (ball c r)) :
    Set.EqOn f₁ f₂ (Ω \ (D₁ ∪ D₂)) := by sorry

end VectorValuedHolomorphy
