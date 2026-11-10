-- Prove2me | Theorems.Thm_RandLatEnum_proposition_7_1
-- name    : RandLatEnum.proposition_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:53.417434+00:00
-- url     : https://prove2.me/theorems/82eebd91-9d32-4bd5-ad68-9f3bda645a46
-- title:
--   Proposition 7.1 (Area rule) — $\mathbb E[F_n(h;L)]=n^{(2A(h)-1/4+o(1))n^2}$; if $A(h)<1/8$, $\Pr[\text{some basis below }h]\le n^{-(1/4-2A(h)+o(1))n^2}$
-- statement:
--   Let $h$ be continuous on $[0,1]$, $A(h)=\int_0^1h$, and $L\sim\mu_n$. Then:
--
--   1. the expected number of admissible complete chains satisfies
--   $$
--   \mathbb E_{\mu_n}[F_n(h;L)]=n^{(2A(h)-1/4+o(1))\,n^2};
--   $$
--   2. if $A(h)<1/8$, the probability that some basis $B$ of $L$ satisfies all the prefix bounds $\det M_k\le n^{n h(k/n)}$, i.e. $P_k(B)\le n\,h(k/n)\ln n$ for $1\le k<n$, is at most
--   $$
--   n^{-(1/4-2A(h)+o(1))\,n^2}.
--   $$
--
--   Each $o(1)$ is a function of $n$ alone tending to $0$. The proposition shows that a prefix profile of area below $1/8$ almost never occurs, for any basis.
--
--   Differences from the source:
--   - encoding: the Haar probability measure µ_n on X_n → any SL_n(ℝ)-invariant Borel probability measure on X_n, taken as a hypothesis; reason: X_n has exactly one such measure (Siegel), so the instances are the same; Mathlib does not construct it
--   - encoding: the probability of an event → the measure of the set, i.e. its outer measure; reason: the paper assumes all choices measurable (p.14); for a measurable set the two agree, and the outer measure is the stronger reading
--   - encoding: the expectation E_{µ_n} → the lower Lebesgue integral ∫⁻ of the [0,∞]-valued integrand; reason: the integrand is nonnegative and measurable (p.14); for measurable integrands ∫⁻ is the expectation
--   - encoding: o(1) in the exponents → ∃ g : ℕ → ℝ with g(n) → 0, the identity (resp. the bound) holding for all large n; reason: definition of o(1)
--   - encoding: a basis satisfies the prefix bounds det M_k ≤ n^{n h(k/n)} → P_k(B) ≤ n h(k/n) ln n for 1 ≤ k < n; reason: det M_k = e^{P_k(B)} for the prefix sublattices ((3.2), p.17)
--   - encoding: a continuous h : [0, 1] → ℝ → h : ℝ → ℝ continuous on [0, 1]; reason: only the values on [0, 1] enter
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Proposition 7.1, (7.2), pp.28–29

import Mathlib
import Definitions.Def_RandLatEnum_X
import Definitions.Def_RandLatEnum_latticeOf
import Definitions.Def_RandLatEnum_IsHaarLatticeMeasure
import Definitions.Def_RandLatEnum_prefixLogDet
import Definitions.Def_RandLatEnum_chainCount
import Definitions.Def_RandLatEnum_areaA

namespace RandLatEnum

open MeasureTheory Filter Topology
open scoped ENNReal

/-- **Proposition 7.1 (Area rule)** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), Proposition 7.1, (7.2), pp.28–29). For every fixed
continuous `h`, `E_{µ_n}[F_n(h; L)] = n^{(2A(h) − 1/4 + o(1)) n²}`. If `A(h) < 1/8`, the probability
that any basis satisfies all these prefix bounds (`det M_k ≤ n^{n h(k/n)}` for its prefix
sublattices `M_k`, i.e. `P_k(B) ≤ n h(k/n) ln n`, `1 ≤ k < n`) is at most
`n^{−(1/4 − 2A(h) + o(1)) n²}`.

**Formalization Note.** `h` is continuous on `[0, 1]`. Each `o(1)` is a function `g(n) → 0` of `n`
alone. `µ_n` is a family of `SL_n(ℝ)`-invariant Borel probability measures; the probability of an
arbitrary set is its outer measure, and the expectation is `∫⁻`. -/
theorem proposition_7_1 (μ : ∀ n : ℕ, Measure (X n)) (hμ : ∀ n, IsHaarLatticeMeasure (μ n))
    (h : ℝ → ℝ) (hh : ContinuousOn h (Set.Icc 0 1)) :
    (∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      ∫⁻ x, ((chainCount n h (latticeOf x) : ℕ∞) : ℝ≥0∞) ∂(μ n) =
        ENNReal.ofReal ((n : ℝ) ^ ((2 * areaA h - 1 / 4 + g n) * (n : ℝ) ^ 2))) ∧
    (areaA h < 1 / 8 → ∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧ ∀ᶠ n : ℕ in atTop,
      μ n {x : X n | ∃ B : Module.Basis (Fin n) ℤ (latticeOf x), ∀ k : ℕ, 1 ≤ k → k < n →
          prefixLogDet (fun i => (B i : EuclideanSpace ℝ (Fin n))) k ≤
            n * h ((k : ℝ) / n) * Real.log n} ≤
        ENNReal.ofReal ((n : ℝ) ^ (-(1 / 4 - 2 * areaA h + g n) * (n : ℝ) ^ 2))) := by sorry

end RandLatEnum
