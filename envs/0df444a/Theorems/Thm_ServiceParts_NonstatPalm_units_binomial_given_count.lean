-- Prove2me | Theorems.Thm_ServiceParts_NonstatPalm_units_binomial_given_count
-- name    : ServiceParts.NonstatPalm.units_binomial_given_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T07:57:06.561121+00:00
-- url     : https://prove2.me/theorems/1752c7e3-7e69-458f-ba53-62a49813b790
-- title:
--   Proof of Theorem 13 — given N(t) = n, the number of units still in resupply at t is binomial(n, p)
-- statement:
--   In the single-location model with nonstationary Poisson demand of rate $\lambda$ and time-dependent resupply distributions $G_s$, fix $t$ with $m(t) > 0$ and let
--   $$p = \int_0^t \bigl(1 - G_s(t-s)\bigr)\frac{\lambda(s)}{m(t)}\,ds,$$
--   the probability that an arbitrary unit demanded during $[0,t)$ is still in resupply at time $t$. Then for all $n, k \ge 0$,
--   $$P\{X(t) = k,\ N(t) = n\} = P\{N(t) = n\}\binom{n}{k} p^k (1-p)^{n-k},$$
--   that is, $P\{X(t) = k \mid N(t) = n\} = \binom{n}{k} p^k (1-p)^{n-k}$ whenever $P\{N(t) = n\} > 0$.
--
--   Combined with the Poisson law of $N(t)$ this yields Theorem 13.
--
--   **Formalization Note** The conditional probability is written as a joint probability, so no division by $P\{N(t) = n\}$ occurs. For $k > n$ the binomial coefficient is $0$, so the natural-number exponent $n - k$ plays no role there.
-- source:
--   Muckstadt, Analysis and Algorithms for Service Parts Supply Chains, Springer 2005, DOI 10.1007/b138879, pp. 216-217, proof of Theorem 13

import Mathlib
import Definitions.Def_ServiceParts_NonstatPalm_ResupplySystem

open MeasureTheory ProbabilityTheory

namespace ServiceParts.NonstatPalm

theorem units_binomial_given_count {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E] (S : ResupplySystem Ω P E)
    {t : ℝ} (hm : 0 < S.meanFn t) (n k : ℕ) :
    (P ({ω | S.unitsInResupply t ω = k} ∩ {ω | S.demandCount t ω = n})).toReal =
      (P {ω | S.demandCount t ω = n}).toReal *
        ((Nat.choose n k : ℝ) *
          (∫ s in (0 : ℝ)..t, (1 - S.resupplyCdf s (t - s)) * (S.rate s / S.meanFn t)) ^ k *
          (1 - ∫ s in (0 : ℝ)..t, (1 - S.resupplyCdf s (t - s)) * (S.rate s / S.meanFn t)) ^
            (n - k)) := by sorry

end ServiceParts.NonstatPalm
