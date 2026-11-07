-- Prove2me | Theorems.Thm_PFRelease_proposition_A_9_lower
-- name    : PFRelease.proposition_A_9_lower
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:44:03.634635+00:00
-- url     : https://prove2.me/theorems/db824d27-8c6a-47c1-b5ee-b08140217f24
-- title:
--   Proposition A.9, lower tail — multiplicative Chernoff bound (upper tail: OfflineStochMatch.Attenuation.lemma_5)
-- statement:
--   Let $N\in\mathbb N$ and let $X_1,\dots,X_N$ be independent Bernoulli random variables, with possibly different parameters. Put $X:=\sum_{i=1}^NX_i$ and $\mu:=\mathbb E[X]$. Then for $0\le u\le1$
--   $$
--   \Pr[X\le(1-u)\mu]\ \le\ \exp\Big(-\frac{u^2\mu}{2}\Big).
--   $$
--   In particular, for every $p\in[0,1]$ the bound applies to $X\sim\mathrm{Bin}(N,p)$ with $\mu=Np$.
--
--   This is the lower tail of Proposition A.9; it is the tail used by target charging (Lemma B.2, with $u=a/(1+a)$). The upper tail $\Pr[X\ge(1+u)\mu]\le\exp(-u^2\mu/(2+u))$ is the published theorem `OfflineStochMatch.Attenuation.lemma_5`, which is part of this mission as a reference item.
--
--   **Formalization Note** Bernoulli variables are measurable, $\{0,1\}$-valued and mutually independent (`iIndepFun`); $\mu$ is the integral of $X$.
--
--   Differences from the source:
--   - encoding: both tails of Proposition A.9 in one statement → the lower tail and its binomial case here; the upper tail is the published companion `OfflineStochMatch.Attenuation.lemma_5` (complement form, $u>0$; the case $u=0$ is trivial); reason: the upper tail is already proved on the platform and is reused, not restated
--   - encoding: independent Bernoulli random variables → measurable real random variables with values in $\{0,1\}$, mutually independent; reason: same objects
--   - encoding: $\mathrm{Bin}(N,p)$ → `PMF.binomial p hp N`; reason: same law
-- source:
--   Shenfeld, Tsfadia, Ligett, Propose-Filter-Release: Scaling Noise to Typical Sensitivity via Private Filtering, arXiv:2610.40654 (held version, sha256 e1d516b3…), Proposition A.9, p.28 (PDF p.30)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace PFRelease

/-- **Proposition A.9 (Multiplicative Chernoff bound), lower tail** (Shenfeld, Tsfadia, Ligett, *Propose-Filter-Release: Scaling Noise to Typical Sensitivity via
Private Filtering*, arXiv:2610.40654 (held version, sha256 e1d516b3…), Proposition A.9,
p.28 = PDF p.30). Given `N ∈ ℕ` and independent Bernoulli random variables `X₁, …, X_N`,
`Pr[X ≤ (1 − u)µ] ≤ exp(−u²µ/2)` for `0 ≤ u ≤ 1`, where `X := Σᵢ Xᵢ` and `µ := E[X]`. In
particular, for every `p ∈ [0, 1]`, the bound applies to `X ∼ Bin(N, p)` with `µ = Np`.

**Formalization Note** The upper tail of Proposition A.9 is the published
`OfflineStochMatch.Attenuation.lemma_5`. Bernoulli variables are measurable real random variables
with values in `{0, 1}` on a probability space, mutually independent (`iIndepFun`), with
arbitrary (possibly different) parameters. `Bin(N, p)` is `PMF.binomial`. -/
theorem proposition_A_9_lower {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (N : ℕ) (X : Fin N → Ω → ℝ) (hXm : ∀ i, Measurable (X i))
    (hX01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (hind : iIndepFun X μ) (u : ℝ) (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1) :
    μ {ω | ∑ i, X i ω ≤ (1 - u) * ∫ ω', ∑ i, X i ω' ∂μ} ≤
        ENNReal.ofReal (Real.exp (-(u ^ 2 * (∫ ω', ∑ i, X i ω' ∂μ) / 2))) ∧
      ∀ (p : NNReal) (hp : p ≤ 1),
        (PMF.binomial p hp N).toOuterMeasure {k | ((k : ℕ) : ℝ) ≤ (1 - u) * (N * (p : ℝ))} ≤
          ENNReal.ofReal (Real.exp (-(u ^ 2 * (N * (p : ℝ)) / 2))) := by sorry

end PFRelease
