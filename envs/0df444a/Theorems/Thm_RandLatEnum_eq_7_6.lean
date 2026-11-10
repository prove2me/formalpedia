-- Prove2me | Theorems.Thm_RandLatEnum_eq_7_6
-- name    : RandLatEnum.eq_7_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:15:09.64008+00:00
-- url     : https://prove2.me/theorems/5c0f55b5-4139-4eb5-a68e-868c3478624a
-- title:
--   Eq. (7.6) — $\inf_B\max_kP_k(B)\ge(c_{\mathrm{flat}}-o(1))\,n\ln n$ with probability $1-o(1)$
-- statement:
--   Let $L\sim\mu_n$. With probability $1-o(1)$,
--   $$
--   \inf_{B\text{ basis of }L}\ \max_{0\le k\le n}P_k(B)\ \ge\ \left(\frac{2-\sqrt2}{4}-o(1)\right)n\ln n ,
--   $$
--   where the error term is independent of the basis: there is one function $g(n)\to0$ such that the probability that some basis $B$ of $L$ has $\max_kP_k(B)<(c_{\mathrm{flat}}-g(n))\,n\ln n$ tends to $0$.
--
--   Combined with Proposition 3.1 this gives Theorem 1.5.
--
--   Differences from the source:
--   - encoding: the Haar probability measure µ_n on X_n → any SL_n(ℝ)-invariant Borel probability measure on X_n, taken as a hypothesis; reason: X_n has exactly one such measure (Siegel), so the instances are the same; Mathlib does not construct it
--   - encoding: the probability of an event → the measure of the set, i.e. its outer measure; reason: the paper assumes all choices measurable (p.14); for a measurable set the two agree, and the outer measure is the stronger reading
--   - encoding: inf_B max_k P_k(B) ≥ (c_flat − o(1)) n ln n with probability 1 − o(1), error independent of the basis → ∃ g → 0 with µ_n{some basis has max_k P_k(B) < (c_flat − g(n)) n ln n} → 0; reason: the infimum is ≥ the bound exactly when no basis is below it; o(1) as a function of n alone
-- source:
--   Laarhoven, Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices, arXiv:2610.15265 (held version, sha256 8fa7a08a…), proof of Theorem 1.5, (7.6), p.29

import Mathlib
import Definitions.Def_RandLatEnum_X
import Definitions.Def_RandLatEnum_latticeOf
import Definitions.Def_RandLatEnum_IsHaarLatticeMeasure
import Definitions.Def_RandLatEnum_maxPrefixLogDet
import Definitions.Def_RandLatEnum_cFlat

namespace RandLatEnum

open MeasureTheory Filter Topology

/-- **Eq. (7.6) (universal prefix lower bound)** (Laarhoven, *Asymptotics of Random-Lattice Enumeration: Beyond HKZ via Dense Sublattices*, arXiv:2610.15265 (held version, sha256 8fa7a08a…), proof of Theorem 1.5, (7.6), p.29). With
probability `1 − o(1)` over `L ∼ µ_n`, `inf_B max_{0≤k≤n} P_k(B) ≥ ((2 − √2)/4 − o(1)) n ln n`, the
infimum over all bases of `L`; the error is independent of the basis.

**Formalization Note.** One `g(n) → 0`, chosen before the lattice and the basis; the bad event
"some basis has `max_k P_k(B) < (c_flat − g(n)) n ln n`" has (outer) `µ_n`-measure tending to `0`. -/
theorem eq_7_6 (μ : ∀ n : ℕ, Measure (X n)) (hμ : ∀ n, IsHaarLatticeMeasure (μ n)) :
    ∃ g : ℕ → ℝ, Tendsto g atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => μ n {x : X n | ∃ B : Module.Basis (Fin n) ℤ (latticeOf x),
          maxPrefixLogDet (fun i => (B i : EuclideanSpace ℝ (Fin n))) <
            (cFlat - g n) * n * Real.log n}) atTop (𝓝 0) := by sorry

end RandLatEnum
