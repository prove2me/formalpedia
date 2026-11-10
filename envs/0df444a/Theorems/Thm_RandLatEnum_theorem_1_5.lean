-- Prove2me | Theorems.Thm_RandLatEnum_theorem_1_5
-- name    : RandLatEnum.theorem_1_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:33.665092+00:00
-- url     : https://prove2.me/theorems/dfe1a35c-136b-4f37-93c7-56aec0e19c54
-- title:
--   Theorem 1.5 — every basis of a Haar-random lattice has $T(B)\ge n^{c_{\mathrm{flat}}n+o(n)}$, $c_{\mathrm{flat}}=(2-\sqrt2)/4$
-- statement:
--   Let $L\sim\mu_n$ be a Haar-random unimodular lattice in $\mathbb R^n$. With probability $1-o(1)$, every basis $B$ of $L$ satisfies
--   $$
--   T(B)\ge n^{c_{\mathrm{flat}}\,n+o(n)},\qquad c_{\mathrm{flat}}=\frac{2-\sqrt2}{4}=0.14644\ldots,
--   $$
--   where $T(B)$ is the number of nodes of the full enumeration tree of $B$ at radius $\lambda_1(L)$. The $o(n)$ is one function $g(n)$ with $g(n)/n\to0$, independent of the lattice and of the basis: the probability that some basis $B$ of $L$ has $T(B)<n^{c_{\mathrm{flat}}n+g(n)}$ tends to $0$.
--
--   This improves the heuristic lower bound $c\ge1/8$ for the enumeration exponent of random lattices to $c\ge(2-\sqrt2)/4$, for all bases simultaneously.
--
--   **Formalization Note** Bases are all ordered $\mathbb Z$-bases of the lattice. The tree counts points in closed balls.
--
--   Differences from the source:
--   - encoding: the Haar probability measure µ_n on X_n → any SL_n(ℝ)-invariant Borel probability measure on X_n, taken as a hypothesis; reason: X_n has exactly one such measure (Siegel), so the instances are the same; Mathlib does not construct it
--   - encoding: the probability of an event → the measure of the set, i.e. its outer measure; reason: the paper assumes all choices measurable (p.14); for a measurable set the two agree, and the outer measure is the stronger reading
--   - encoding: T(B) ≥ n^{c_flat n + o(n)} with probability 1 − o(1) for every basis → ∃ g with g(n)/n → 0 such that µ_n{some basis has T(B) < n^{c_flat n + g(n)}} → 0; reason: o(n) as one function of n alone, independent of the basis (p.29: the error is independent of the basis)
--   - encoding: nodes of the full enumeration tree at radius λ₁(L) → 1 + Σ_d #(π_{n−d+1}(L) ∩ closed ball of radius λ₁(L)), counted with Set.ncard; reason: (3.1), p.17; the tree at radius R contains the vectors of norm ≤ R
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Theorem 1.5, (1.6), p.5; (1.1), p.2; (3.1), p.17

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_RandLatEnum_X
import Definitions.Def_RandLatEnum_latticeOf
import Definitions.Def_RandLatEnum_IsHaarLatticeMeasure
import Definitions.Def_RandLatEnum_treeSize
import Definitions.Def_RandLatEnum_cFlat

namespace RandLatEnum

open MeasureTheory Filter Topology KannanLattice.Core

/-- **Theorem 1.5 (Tree size lower bound)** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Theorem 1.5, (1.6), p.5). With probability
`1 − o(1)` over `L ∼ µ_n`, every basis `B` of `L` satisfies `T(B) ≥ n^{c_flat·n + o(n)}`, with
`c_flat = (2 − √2)/4`, where `T(B)` is the number of nodes of the full enumeration tree of `B` at
radius `λ₁(L)` ((1.1), p.2; (3.1), p.17).

**Formalization Note.** The `o(n)` is one function `g(n)` with `g(n)/n → 0`, chosen before the
lattice and the basis. The bad event "some ordered `ℤ`-basis of `L` has `T(B) < n^{c_flat n + g(n)}`"
has (outer) `µ_n`-measure tending to `0`. `µ_n` is a family of `SL_n(ℝ)`-invariant Borel probability
measures on `X_n = SL_n(ℝ)/SL_n(ℤ)`. -/
theorem theorem_1_5 (μ : ∀ n : ℕ, Measure (X n)) (hμ : ∀ n, IsHaarLatticeMeasure (μ n)) :
    ∃ g : ℕ → ℝ, Tendsto (fun n : ℕ => g n / n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => μ n {x : X n | ∃ B : Module.Basis (Fin n) ℤ (latticeOf x),
          (treeSize (fun i => (B i : EuclideanSpace ℝ (Fin n)))
              (lambdaOne (latticeOf x : Set (EuclideanSpace ℝ (Fin n)))) : ℝ) <
            (n : ℝ) ^ (cFlat * n + g n)}) atTop (𝓝 0) := by sorry

end RandLatEnum
