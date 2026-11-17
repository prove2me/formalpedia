-- Prove2me | Theorems.Thm_RandLatEnum_Supplement_theorem_1_1
-- name    : RandLatEnum.Supplement.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:02:15.423212+00:00
-- url     : https://prove2.me/theorems/396a0d86-4cbb-4f94-a818-19b5b09e85f8
-- title:
--   Theorem 1.1 — every quasi-HKZ basis has $T(B)=n^{n/(2e)+o(n)}$
-- statement:
--   Let $L\sim\mu_n$ be a Haar-random unimodular lattice in $\mathbb R^n$, and for a basis $B$ of $L$ let $T(B)$ be the number of nodes of the full enumeration tree of $B$ at radius $\lambda_1(L)$. With probability $1-o(1)$, every quasi-HKZ basis $B$ of $L$ satisfies
--   $$T(B)=n^{c_{\mathrm{HKZ}}\,n+o(n)},\qquad c_{\mathrm{HKZ}}=\frac1{2e}=0.18393\ldots$$
--
--   The $o(n)$ term is uniform over all quasi-HKZ bases of $L$. This confirms, for random lattices, the heuristic HKZ geometry of Hanrot–Pujol–Stehlé and Haque–Pieprzyk and the tree-size exponent conjectured by Hanrot–Stehlé, and is the baseline the split constructions of Theorems 1.2–1.4 improve.
--
--   Differences from the source:
--   - encoding: L ∼ µ_n, the Haar probability measure on X_n = SL_n(ℝ)/SL_n(ℤ) → a family μ n of SL_n(ℝ)-invariant Borel probability measures on X n (hypothesis IsHaarLatticeMeasure), L = latticeOf x; reason: there is exactly one such measure (Siegel); same convention as the published goal RandLatEnum.theorem_1_5
--   - encoding: with probability 1 − o(1) → the outer µ_n-measure of the bad event tends to 0; reason: same convention as the published goal; equal to the probability for measurable events and never weaker
--   - encoding: = n^{c n + o(n)} → one g : ℕ → ℝ with g(n)/n → 0, chosen before the lattice and the basis, and n^{c n − g(n)} ≤ T ≤ n^{c n + g(n)}; reason: one g for both sides is equivalent to two o(n) terms (take the larger in absolute value)
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08adef70deb2f23a9a830e01c5a5b031ddaf5e0d4f88ce5174d67214b37), Theorem 1.1, (1.2), p.4 (proof §4.4, (4.14), p.21)

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_RandLatEnum_X
import Definitions.Def_RandLatEnum_latticeOf
import Definitions.Def_RandLatEnum_IsHaarLatticeMeasure
import Definitions.Def_RandLatEnum_treeSize
import Definitions.Def_RandLatEnum_Supplement_IsQuasiHKZ

namespace RandLatEnum.Supplement

open MeasureTheory Filter Topology KannanLattice.Core RandLatEnum

/-- **Theorem 1.1 (Tree size of all quasi-HKZ bases)** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Theorem 1.1, (1.2), p.4;
proof §4.4, p.21). With probability `1 − o(1)` over `L ∼ µ_n`, every quasi-HKZ basis `B` of `L`
has enumeration tree size `T(B) = n^{c_HKZ·n + o(n)}`, `c_HKZ = 1/(2e)`.

**Formalization Note.** `µ_n` is a family of `SL_n(ℝ)`-invariant Borel probability measures on `X_n` (unique, hence Haar); `L = latticeOf x`; bases are ordered `ℤ`-bases of `L` coerced to `ℝⁿ`. The `o(n)` is one function `g` with `g(n)/n → 0`, chosen before the lattice and the basis; "with probability `1 − o(1)`" is: the (outer) `µ_n`-measure of the bad event tends to `0`. The two-sided `=` is `n^{c n − g(n)} ≤ T(B) ≤ n^{c n + g(n)}`; the bad
event is "some quasi-HKZ basis violates it". `T(B)` is the published `treeSize` at radius
`λ₁(L)`. -/
theorem theorem_1_1 (μ : ∀ n : ℕ, Measure (X n)) (hμ : ∀ n, IsHaarLatticeMeasure (μ n)) :
    ∃ g : ℕ → ℝ, Tendsto (fun n : ℕ => g n / n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => μ n {x : X n | ∃ B : Module.Basis (Fin n) ℤ (latticeOf x),
          IsQuasiHKZ (fun i => (B i : EuclideanSpace ℝ (Fin n))) ∧
          ¬ ((n : ℝ) ^ (1 / (2 * Real.exp 1) * n - g n) ≤
                (treeSize (fun i => (B i : EuclideanSpace ℝ (Fin n)))
                  (lambdaOne (latticeOf x : Set (EuclideanSpace ℝ (Fin n)))) : ℝ) ∧
              (treeSize (fun i => (B i : EuclideanSpace ℝ (Fin n)))
                  (lambdaOne (latticeOf x : Set (EuclideanSpace ℝ (Fin n)))) : ℝ) ≤
                (n : ℝ) ^ (1 / (2 * Real.exp 1) * n + g n))}) atTop (𝓝 0) := by sorry

end RandLatEnum.Supplement
