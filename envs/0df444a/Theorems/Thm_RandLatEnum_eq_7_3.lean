-- Prove2me | Theorems.Thm_RandLatEnum_eq_7_3
-- name    : RandLatEnum.eq_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:16:12.624471+00:00
-- url     : https://prove2.me/theorems/94f1dbab-f95b-42e0-a767-03390f040966
-- title:
--   Eq. (7.3) — Kim's formula $\mathbb E_{\mu_n}[F_n(h;L)]=\frac{n!}{2^{n-1}}\prod_{d=2}^n\kappa_d\,e^{2n\ln n\sum_k h(k/n)}$
-- statement:
--   Let $n\ge2$ and let $L\sim\mu_n$ be a Haar-random unimodular lattice. For every ceiling $h$, the expected number of admissible complete chains (7.1) is
--   $$
--   \mathbb E_{\mu_n}[F_n(h;L)]=\frac{n!}{2^{n-1}}\left(\prod_{d=2}^{n}\kappa_d\right)\exp\!\left(2n\ln n\sum_{k=1}^{n-1}h(k/n)\right),
--   $$
--   with $\kappa_d=V_d/(2\zeta(d))$. This is Kim's mean-value formula for flags of primitive sublattices [Kim, Theorem 5], specialized to the complete rank sequence $(1,\dots,n-1)$, where all determinant powers equal two.
--
--   It is the exact first-moment identity behind the area rule.
--
--   **Formalization Note** The count takes values in the extended naturals.
--
--   Differences from the source:
--   - generalization: a fixed continuous ceiling h → every function h : ℝ → ℝ (only the values h(k/n), 1 ≤ k < n, enter); reason: Kim's formula holds for any positive determinant thresholds n^{n h(k/n)}; continuous h is the printed case
--   - encoding: the Haar probability measure µ_n on X_n → any SL_n(ℝ)-invariant Borel probability measure on X_n, taken as a hypothesis; reason: X_n has exactly one such measure (Siegel), so the instances are the same; Mathlib does not construct it
--   - encoding: the expectation E_{µ_n} → the lower Lebesgue integral ∫⁻ of the [0,∞]-valued integrand; reason: the integrand is nonnegative and measurable (p.14); for measurable integrands ∫⁻ is the expectation
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), proof of Proposition 7.1, (7.3), p.29 (citing Kim [35, Theorem 5])

import Mathlib
import Definitions.Def_RandLatEnum_X
import Definitions.Def_RandLatEnum_latticeOf
import Definitions.Def_RandLatEnum_IsHaarLatticeMeasure
import Definitions.Def_RandLatEnum_kappa
import Definitions.Def_RandLatEnum_chainCount

namespace RandLatEnum

open MeasureTheory
open scoped ENNReal

/-- **Eq. (7.3) (Kim's formula for complete chains)** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), proof of Proposition 7.1, (7.3), p.29,
citing Kim [35, Theorem 5]). For the complete rank sequence `(1, …, n − 1)`,
`E_{µ_n}[F_n(h; L)] = (n!/2^{n−1}) (∏_{d=2}^{n} κ_d) exp(2n ln n Σ_{k=1}^{n−1} h(k/n))`.

**Formalization Note.** `µ_n` is any `SL_n(ℝ)`-invariant Borel probability measure on `X_n` (unique).
The expectation of the `ℕ∞`-valued count is the lower Lebesgue integral `∫⁻`. The identity is
stated for every ceiling `h : ℝ → ℝ` (only the values `h(k/n)`, `1 ≤ k < n`, enter). -/
theorem eq_7_3 (n : ℕ) (hn : 2 ≤ n) (μ : Measure (X n)) (hμ : IsHaarLatticeMeasure μ)
    (h : ℝ → ℝ) :
    ∫⁻ x, ((chainCount n h (latticeOf x) : ℕ∞) : ℝ≥0∞) ∂μ =
      ENNReal.ofReal ((n.factorial : ℝ) / 2 ^ (n - 1) * (∏ d ∈ Finset.Icc 2 n, kappa d) *
        Real.exp (2 * n * Real.log n * ∑ k ∈ Finset.Icc 1 (n - 1), h ((k : ℝ) / n))) := by sorry

end RandLatEnum
