-- Prove2me | Theorems.Thm_RandLatEnum_Supplement_theorem_1_6
-- name    : RandLatEnum.Supplement.theorem_1_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:05:09.030255+00:00
-- url     : https://prove2.me/theorems/ccc54ed6-4430-4d8d-8a0e-7751614eb4e4
-- title:
--   Theorem 1.6 — for every basis, $\sqrt{P(B)}\ge n^{(2-\sqrt2)n/8+o(n)}$
-- statement:
--   Let $L\sim\mu_n$ and, for a basis $B$ of $L$ with Gram–Schmidt lengths $a_i$, let $P(B)=\prod_{i=1}^n\max\{1,a_i^{-1}\}$ be the Feng–Gao–Liu geometric product. With probability $1-o(1)$, simultaneously for every basis $B$ of $L$,
--   $$\sqrt{P(B)}\ \ge\ n^{\tau_{\mathrm{low}}\,n+o(n)},\qquad \tau_{\mathrm{low}}=\frac{2-\sqrt2}{8}=0.07322\ldots$$
--
--   The $o(n)$ term does not depend on the basis. This transfers the universal lower bound of Theorem 1.5 to the geometric factor of the Feng–Gao–Liu collision search, with the constant halved; it bounds that factor, not the algorithm's running time.
--
--   Differences from the source:
--   - encoding: L ∼ µ_n, the Haar probability measure on X_n = SL_n(ℝ)/SL_n(ℤ) → a family μ n of SL_n(ℝ)-invariant Borel probability measures on X n (hypothesis IsHaarLatticeMeasure), L = latticeOf x; reason: there is exactly one such measure (Siegel); same convention as the published goal RandLatEnum.theorem_1_5
--   - encoding: with probability 1 − o(1) → the outer µ_n-measure of the bad event tends to 0; reason: same convention as the published goal; equal to the probability for measurable events and never weaker
--   - encoding: o(n) in the exponent → one g : ℕ → ℝ with g(n)/n → 0, chosen before the lattice and the basis; reason: same convention as the published goal
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08adef70deb2f23a9a830e01c5a5b031ddaf5e0d4f88ce5174d67214b37), Theorem 1.6, (1.9), p.6 (P(B) at (8.4), p.31; proof §8.2, (8.5), p.32)

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice
import Definitions.Def_RandLatEnum_X
import Definitions.Def_RandLatEnum_latticeOf
import Definitions.Def_RandLatEnum_IsHaarLatticeMeasure
import Definitions.Def_RandLatEnum_Supplement_fglProduct

namespace RandLatEnum.Supplement

open MeasureTheory Filter Topology KannanLattice.Core RandLatEnum

/-- **Theorem 1.6 (Collision search cost factor lower bound)** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Theorem 1.6, (1.9),
p.6; proof §8.2, p.32). With probability `1 − o(1)` over `L ∼ µ_n`, simultaneously for every basis
`B` of `L`, `√P(B) ≥ n^{τ_low·n + o(n)}`, `τ_low = (2 − √2)/8`.

**Formalization Note.** `µ_n` is a family of `SL_n(ℝ)`-invariant Borel probability measures on `X_n` (unique, hence Haar); `L = latticeOf x`; bases are ordered `ℤ`-bases of `L` coerced to `ℝⁿ`. The `o(n)` is one function `g` with `g(n)/n → 0`, chosen before the lattice and the basis; "with probability `1 − o(1)`" is: the (outer) `µ_n`-measure of the bad event tends to `0`. The bad event is "some basis has `√P(B) < n^{τ_low n + g(n)}`".
`P(B)` is `fglProduct` ((8.4), p.31). -/
theorem theorem_1_6 (μ : ∀ n : ℕ, Measure (X n)) (hμ : ∀ n, IsHaarLatticeMeasure (μ n)) :
    ∃ g : ℕ → ℝ, Tendsto (fun n : ℕ => g n / n) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => μ n {x : X n | ∃ B : Module.Basis (Fin n) ℤ (latticeOf x),
          Real.sqrt (fglProduct (fun i => (B i : EuclideanSpace ℝ (Fin n)))) <
            (n : ℝ) ^ ((2 - Real.sqrt 2) / 8 * n + g n)}) atTop (𝓝 0) := by sorry

end RandLatEnum.Supplement
