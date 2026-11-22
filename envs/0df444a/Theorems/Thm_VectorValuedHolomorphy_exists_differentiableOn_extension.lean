-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_exists_differentiableOn_extension
-- name    : VectorValuedHolomorphy.exists_differentiableOn_extension
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:49:17.730866+00:00
-- url     : https://prove2.me/theorems/38b5d069-18bb-44c5-99ec-e19adca12192
-- title:
--   Riemann's removable singularity theorem for holomorphic functions with values in a quasi-complete locally convex space
-- statement:
--   **Riemann's theorem on removable singularities, vector-valued version.**
--
--   Let $E$ be a quasi-complete Hausdorff locally convex topological vector space over $\mathbb C$. Let $U\subset\mathbb C$ be open, let $Z$ be a discrete subset of $U$, closed in $U$ (that is, $Z$ has no accumulation point in $U$), and let $f:U\setminus Z\to E$ be holomorphic (complex differentiable, the difference quotients converging in $E$). Assume that $f$ is locally bounded near every point of $U$: every $z\in U$ lies in an open disc $B\subset U$ such that
--   $$f(B\setminus Z)\ \text{is a bounded subset of }E$$
--   (bounded in the sense of topological vector spaces: absorbed by every neighbourhood of $0$).
--
--   Then $f$ extends to a holomorphic function $g:U\to E$, and the extension is unique:
--   $$\exists!\ g:U\to E\ \text{holomorphic with}\ g|_{U\setminus Z}=f .$$
--
--   This is the analogue of Riemann's theorem for functions with values in spaces of distributions or operators. Quasi-completeness is what guarantees that the limit value at a point of $Z$ is a vector of $E$ and not merely a linear form on $E'$. The paper records it in §C.5.4, next to its vector-valued Residue Theorem and Identity Theorem.
--
--   **Formalization Note.** `E` is a complex vector space with a uniform structure making it a uniform additive group (`[UniformSpace E] [IsUniformAddGroup E]`), with continuous scalar multiplication, locally convex in the sense of Mathlib's `PolynormableSpace ℂ E` (the topology is defined by a family of seminorms), Hausdorff (`T2Space`) and quasi-complete (`QuasiCompleteSpace ℂ E`: closed von Neumann bounded sets are complete). The continuous dual $E'$ is `StrongDual ℂ E`. Holomorphy of an $E$-valued function is Mathlib's `DifferentiableOn ℂ f U` / `deriv`, which at the pinned Mathlib are defined for topological vector space targets and mean convergence of the difference quotients in $E$ (`Asymptotics.isLittleOTVS_iff_tendsto_inv_smul`). Functions are total maps `ℂ → E`; only their values on the open set matter. The condition on `Z` is `∀ z ∈ U, ∀ᶠ w in 𝓝[≠] z, w ∉ Z` (no accumulation point of `Z` in `U`); `Z ⊆ U` is not required since only `Z ∩ U` matters. Boundedness is `Bornology.IsVonNBounded ℂ (f '' (ball c r \ Z))` for some disc `ball c r ⊆ U` containing the point. Since `g : ℂ → E` is a total function, "unique extension" is expressed as: there is `g` holomorphic on `U` agreeing with `f` on `U \ Z`, and every `g'` with these two properties agrees with `g` on `U`. The source assumes $U$ connected, which plays no role, and writes "discrete subset"; holomorphy on $U\setminus Z$ requires this set to be open, whence the reading "closed and discrete in $U$".
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 741, Lemma C.5.4.2 (On removable singularities); classical reference (cited by the paper at this spot): K. Kruse, Vector-valued holomorphic functions in several variables, Theorem 7.4

import Mathlib

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace VectorValuedHolomorphy

theorem exists_differentiableOn_extension {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] {U Z : Set ℂ} (hU : IsOpen U)
    (hZ : ∀ z ∈ U, ∀ᶠ w in 𝓝[≠] z, w ∉ Z) {f : ℂ → E} (hf : DifferentiableOn ℂ f (U \ Z))
    (hb : ∀ z ∈ U, ∃ (c : ℂ) (r : ℝ), z ∈ ball c r ∧ ball c r ⊆ U ∧
      Bornology.IsVonNBounded ℂ (f '' (ball c r \ Z))) :
    ∃ g : ℂ → E, DifferentiableOn ℂ g U ∧ Set.EqOn g f (U \ Z) ∧
      ∀ g' : ℂ → E, DifferentiableOn ℂ g' U → Set.EqOn g' f (U \ Z) → Set.EqOn g' g U := by
  sorry

end VectorValuedHolomorphy
