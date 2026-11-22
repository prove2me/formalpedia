-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_hasOrderAt_iff_exists_laurent
-- name    : VectorValuedHolomorphy.hasOrderAt_iff_exists_laurent
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:25:07.847901+00:00
-- url     : https://prove2.me/theorems/9ccc747a-9ab2-4f57-a5ad-3b28a5c780bf
-- title:
--   Order of a vector-valued function at a point: the factorized form agrees with the Laurent-series form of Definition C.5.3.1(1) (first exponent with a non-zero coefficient)
-- statement:
--   **The order at a point is the first exponent of the Laurent expansion.** Let $E$ be a quasi-complete Hausdorff locally convex space over $\mathbb C$, let $z_0\in\mathbb C$, $n\in\mathbb Z$, and let $f$ be an $E$-valued function defined on a punctured neighbourhood of $z_0$. Recall that $f$ *has order $n$ at $z_0$* if $f(z)=(z-z_0)^n g(z)$ for $z\ne z_0$ near $z_0$, with $g$ holomorphic on a neighbourhood of $z_0$ and $g(z_0)\neq 0$.
--
--   The theorem states that $f$ has order $n$ at $z_0$ if and only if there are vectors $a_n,a_{n+1},\dots\in E$ with
--   $$a_n\neq 0$$
--   and a radius $R>0$ such that
--   $$f(z)=\sum_{k\ge n}a_k\,(z-z_0)^{k}\qquad(0<|z-z_0|<R),$$
--   the series converging in $E$ uniformly on every compact subset of the punctured disc $\{0<|z-z_0|<R\}$.
--
--   This identifies the factorized definition of the order with the definition by Laurent series of the paper (Definition C.5.3.1(1): the order is the index at which the Laurent expansion starts), and in particular a pole of order $m\ge 1$ is a point where the expansion starts at $(z-z_0)^{-m}$ with a non-zero coefficient. The paper does not state this equivalence as a numbered result: it defines the order through the Laurent series (Definition C.5.3.1(1), in the corrected reading), whereas the definition file takes the factorized form; the statement shows that the two definitions agree when $E$ is a quasi-complete Hausdorff locally convex space.
--
--   **Formalization Note.** `HasOrderAt` is `VectorValuedHolomorphy.HasOrderAt` from the definition file. The coefficients are indexed by `ℕ`: `a j` is the coefficient of $(z-z_0)^{n+j}$ (an integer power `(z - z₀) ^ (n + (j : ℤ))`), the condition $a_n\ne0$ is `a 0 ≠ 0`, and the convergence is `TendstoUniformlyOn` of the partial sums over `Finset.range m` on every compact `K ⊆ ball z₀ R \ {z₀}`. "Quasi-complete Hausdorff locally convex space" is `[UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E] [QuasiCompleteSpace ℂ E]`. The value of `f` at `z₀` is irrelevant on both sides. **Deviation from the source.** Definition C.5.3.1(1) prints "the minimal integer $N$" for which a Laurent expansion starting at $N$ exists, which has no meaning as printed; the statement here uses the classical notion (first non-zero coefficient).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 739, Definition C.5.3.1(1)-(2), formulas (C.5.3.1)-(C.5.3.2)

import Mathlib
import Definitions.Def_VectorValuedHolomorphy_Order

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace VectorValuedHolomorphy

/-- A function with values in a quasi-complete Hausdorff locally convex space has order `n` at
`z₀` iff it has a Laurent expansion at `z₀` starting at the exponent `n` with a non-zero
coefficient. -/
theorem hasOrderAt_iff_exists_laurent {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] (f : ℂ → E) (z₀ : ℂ) (n : ℤ) :
    HasOrderAt f z₀ n ↔
      ∃ (a : ℕ → E) (R : ℝ), a 0 ≠ 0 ∧ 0 < R ∧
        ∀ K : Set ℂ, IsCompact K → K ⊆ ball z₀ R \ {z₀} →
          TendstoUniformlyOn
            (fun (m : ℕ) (z : ℂ) =>
              ∑ j ∈ Finset.range m, (z - z₀) ^ (n + (j : ℤ)) • a j)
            f atTop K := by sorry

end VectorValuedHolomorphy
