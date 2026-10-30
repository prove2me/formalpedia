-- Prove2me | Theorems.Thm_WassersteinDRO_GelbrichFiniteSample_theorem_21_concentration_mean_cov
-- name    : WassersteinDRO.GelbrichFiniteSample.theorem_21_concentration_mean_cov
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:59:53.849249+00:00
-- url     : https://prove2.me/theorems/6af67c7b-7e97-4bbe-b4fe-e8db16bcde5a
-- title:
--   Theorem 21: $(\mu, \Sigma) \in \mathcal U_\varepsilon(\widehat\mu, \widehat\Sigma)$ with probability $\ge 1 - \eta$ for $\varepsilon \ge \log(c/\eta)/\sqrt N$
-- statement:
--   Let $m \in \mathbb N$, $\alpha > 2$, $A > 0$, $\mu \in \mathbb R^m$ and let $\Sigma$ be an $m \times m$ matrix. There is a constant $c > 1$, depending only on $m, \alpha, A, \mu, \Sigma$, with the following property.
--
--   Let $\mathbb P$ be any probability distribution on $\mathbb R^m$ with mean vector $\mu$ and covariance matrix $\Sigma$ such that
--
--   $$\mathbb E^{\mathbb P}\big[\exp(\|\xi\|_2^\alpha)\big] \le A.$$
--
--   Let $\widehat\xi_1, \dots, \widehat\xi_N$ ($N \ge 1$) be drawn independently from $\mathbb P$, and let $\widehat\mu$ and $\widehat\Sigma$ be their sample mean and sample covariance matrix (normalized by $1/N$). Then for every $\eta \in (0, 1]$ and every
--
--   $$\varepsilon \ge \varepsilon_N(\eta) = \frac{\log(c/\eta)}{\sqrt N},$$
--
--   we have
--
--   $$\mathbb P^N\big[(\mu, \Sigma) \in \mathcal U_\varepsilon(\widehat\mu, \widehat\Sigma)\big] \ge 1 - \eta.$$
--
--   The uncertainty set around the sample moments is therefore a $(1 - \eta)$-confidence set for the true mean and covariance, with a radius of order $N^{-1/2}$ that does not deteriorate with the dimension. This is the probabilistic ingredient of Theorem 22.
--
--   **Formalization Note** The probability bound is stated as: some measurable set of samples contained in the event has $\mathbb P^N$-probability at least $1 - \eta$. The moment condition is an integral of a nonnegative function in $[0, \infty]$.
--
--   Differences from the source:
--   - reading: "whenever ε exceeds εN(η)" → ε ≥ log(c/η)/√N; reason: the two readings are equivalent (the event at ε_N(η) is the decreasing limit of the events for ε ↓ ε_N(η), and P^N is continuous from above); ≥ is the non-weaker form and is the one Theorem 22 uses.
--   - reading: P^N[(µ, Σ) ∈ Uε(µ̂, Σ̂)] ≥ 1 − η → some measurable set S inside the event has P^N(S) ≥ 1 − η (inner measure); reason: this is never weaker than the outer-measure value of the event and agrees with P^N of the event whenever it is measurable.
--   - encoding: c > 1 depends on P only through µ, Σ, α, A, and m → ∃ c with 1 < c placed after m, α, A, µ, Σ and before P, N, η, ε; reason: quantifier order expresses exactly this dependence.
--   - encoding: P has mean vector µ and covariance matrix Σ → HasMeanCov P µ Σ, which includes a finite second moment of ξ; reason: having a covariance matrix presupposes finite second moments, and they follow from the moment bound; no instance is lost.
--   - encoding: E^P[exp(‖ξ‖₂^α)] ≤ A → ∫⁻ ofReal(exp(‖ξ‖^α)) dP ≤ ofReal A on EuclideanSpace ℝ (Fin m); reason: the lower Lebesgue integral of a positive function is its expectation, with no integrability side condition; the norm of EuclideanSpace is ‖·‖₂.
--   - encoding: N independent training samples, εN(η) = log(c/η)/√N → N ≥ 1 samples in Fin N → ℝ^m under the product measure Measure.pi (fun _ => P); reason: the samples are indexed by i ∈ {1, …, N} and ε_N divides by √N.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, Theorem 21 (Concentration inequalities II), eq. (28), p. 23

import Mathlib
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_HasMeanCov
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_sampleMean
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_sampleCov
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_uncertaintySet

open MeasureTheory

namespace WassersteinDRO.GelbrichFiniteSample

/-- **Theorem 21 (Concentration inequalities II).**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, Theorem 21, eq. (28), p. 23: "Suppose that the unknown true distribution P has mean vector µ
and covariance matrix Σ and that there are α > 2 and A > 0 such that E^P[exp(‖ξ‖₂^α)] ≤ A. Then,
there is c > 1 that depends on P only through µ, Σ, α, A, and m such that for any η ∈ (0,1] the
sample mean µ̂ and the sample covariance matrix Σ̂ satisfy the concentration inequality
P^N[(µ, Σ) ∈ U_ε(µ̂, Σ̂)] ≥ 1 − η whenever ε exceeds ε_N(η) = log(c/η)/√N. (28)"

For every dimension `m`, `α > 2`, `A > 0`, `µ ∈ ℝ^m` and `m × m` matrix `Σ` there is `c > 1` such
that for every probability measure `P` on `ℝ^m` with mean `µ`, covariance `Σ` and
`∫ exp(‖ξ‖₂^α) dP ≤ A`, every `N ≥ 1`, `η ∈ (0, 1]` and `ε ≥ log(c/η)/√N`, the event that `(µ, Σ)`
lies in `U_ε(µ̂, Σ̂)` (with `µ̂, Σ̂` the sample mean and covariance of `N` iid draws from `P`)
contains a measurable set of `P^N`-probability at least `1 − η`.

**Formalization Note.** (1) "c depends on P only through µ, Σ, α, A, and m" is encoded by quantifier
order: `∃ c` comes after `m α A µ Σ` and before `P`, `N`, `η`, `ε`. (2) "ε exceeds ε_N(η)" is read as
`ε ≥ ε_N(η)`, the non-weaker reading (equivalent to `>` by continuity of `P^N` from above).
(3) `P^N[E] ≥ 1 − η` is stated as an inner-measure bound: some measurable `S ⊆ E` has
`P^N(S) ≥ 1 − η`; this is never weaker than the outer-measure value. (4) The moment condition is a
`lintegral` of the positive function `exp(‖ξ‖₂^α)`, so it is the exact expectation. (5) "has mean
vector µ and covariance matrix Σ" includes finite second moments (`HasMeanCov`), which the moment
condition implies. (6) The `N` samples are `Fin N → ℝ^m` under the product measure `P^N`
(`Measure.pi`), and `N ≥ 1`. -/
theorem theorem_21_concentration_mean_cov (m : ℕ) (α A : ℝ) (hα : 2 < α) (hA : 0 < A)
    (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ) :
    ∃ c : ℝ, 1 < c ∧
      ∀ (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P],
        HasMeanCov P μ Sig →
        ∫⁻ ξ, ENNReal.ofReal (Real.exp (‖ξ‖ ^ α)) ∂P ≤ ENNReal.ofReal A →
        ∀ (N : ℕ), 0 < N → ∀ (η : ℝ), 0 < η → η ≤ 1 →
        ∀ (ε : ℝ), Real.log (c / η) / Real.sqrt N ≤ ε →
        ∃ S : Set (Fin N → EuclideanSpace ℝ (Fin m)), MeasurableSet S ∧
          S ⊆ {ξh | (μ, Sig) ∈ uncertaintySet ε (sampleMean ξh) (sampleCov ξh)} ∧
          ENNReal.ofReal (1 - η) ≤ Measure.pi (fun _ : Fin N => P) S := by sorry

end WassersteinDRO.GelbrichFiniteSample
