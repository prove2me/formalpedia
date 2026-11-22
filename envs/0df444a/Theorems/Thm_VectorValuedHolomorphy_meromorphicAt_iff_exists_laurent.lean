-- Prove2me | Theorems.Thm_VectorValuedHolomorphy_meromorphicAt_iff_exists_laurent
-- name    : VectorValuedHolomorphy.meromorphicAt_iff_exists_laurent
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T10:50:47.991987+00:00
-- url     : https://prove2.me/theorems/5f8231d0-3c5b-4ff6-b6de-bb44fe76c826
-- title:
--   A vector-valued function is meromorphic at $z_0$ iff it has a Laurent expansion with finite principal part, uniformly convergent on compact subsets of a punctured disc
-- statement:
--   **Laurent expansion characterizes vector-valued meromorphy.**
--
--   Let $E$ be a quasi-complete Hausdorff locally convex topological vector space over $\mathbb C$, let $z_0\in\mathbb C$ and let $f$ be an $E$-valued function defined on a punctured neighbourhood of $z_0$. Recall that $f$ is *meromorphic at $z_0$* if for some integer $n\ge 0$ the function $(z-z_0)^n f(z)$ extends to a function holomorphic on a neighbourhood of $z_0$.
--
--   The theorem states that $f$ is meromorphic at $z_0$ if and only if it has a Laurent expansion with only finitely many negative exponents: there exist an integer $N\ge 0$, vectors $a_{-N},a_{-N+1},\dots\in E$ and a radius $R>0$ such that
--   $$f(z)=\sum_{k\ge -N}a_k\,(z-z_0)^{k}\qquad(0<|z-z_0|<R),$$
--   the series converging in $E$ uniformly on every compact subset $K$ of the punctured disc $\{0<|z-z_0|<R\}$ (the partial sums $\sum_{-N\le k<n-N}a_k(z-z_0)^k$ converge to $f$ uniformly on $K$ as $n\to\infty$).
--
--   This is the equivalence asserted inside the paper's Definition C.5.3.1 of meromorphic $E$-valued functions ("the series converges uniformly over the compact subsets of a punctured neighborhood … equivalently, some $(\xi-\xi_0)^{N}f(\xi)$ extends holomorphically across $\xi_0$"). The coefficients $a_k(z_0,f)$ are the Laurent coefficients, and $a_{-1}$ is the residue.
--
--   **Formalization Note.** `E` is a complex vector space with a uniform structure making it a uniform additive group (`[UniformSpace E] [IsUniformAddGroup E]`), with continuous scalar multiplication, locally convex in the sense of Mathlib's `PolynormableSpace ℂ E` (the topology is defined by a family of seminorms), Hausdorff (`T2Space`) and quasi-complete (`QuasiCompleteSpace ℂ E`: closed von Neumann bounded sets are complete). The continuous dual $E'$ is `StrongDual ℂ E`. `MeromorphicAt` is `VectorValuedHolomorphy.MeromorphicAt` from the definition file (pole-clearing form). The Laurent coefficients are indexed by `ℕ` with a shift: `a j` is the coefficient of $(z-z_0)^{j-N}$, the power being an integer power `(z - z₀) ^ ((j : ℤ) - (N : ℤ))`; uniform convergence of the partial sums over `Finset.range n` on a compact `K ⊆ ball z₀ R \ {z₀}` is Mathlib's `TendstoUniformlyOn`. The value of `f` at `z₀` is irrelevant on both sides. **Deviation from the source.** Definition C.5.3.1 prints the lowest index of the series as an integer "$k\ge 0$", which would exclude poles and contradicts both the pole-clearing clause and (C.5.3.4), where the series starts at $-N$; the corrected statement, with an arbitrary lowest index $-N\le 0$, is formalized.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 739-740, Definition C.5.3.1 (the equivalence stated in the definition), formulas (C.5.3.1)-(C.5.3.2) and (C.5.3.4)

import Mathlib
import Definitions.Def_VectorValuedHolomorphy_Meromorphic

open Filter Topology Metric
open scoped Real

set_option autoImplicit false

namespace VectorValuedHolomorphy

theorem meromorphicAt_iff_exists_laurent {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E]
    [T2Space E] [QuasiCompleteSpace ℂ E] (f : ℂ → E) (z₀ : ℂ) :
    MeromorphicAt f z₀ ↔
      ∃ (N : ℕ) (a : ℕ → E) (R : ℝ), 0 < R ∧
        ∀ K : Set ℂ, IsCompact K → K ⊆ ball z₀ R \ {z₀} →
          TendstoUniformlyOn
            (fun (n : ℕ) (z : ℂ) =>
              ∑ j ∈ Finset.range n, (z - z₀) ^ ((j : ℤ) - (N : ℤ)) • a j)
            f atTop K := by sorry

end VectorValuedHolomorphy
