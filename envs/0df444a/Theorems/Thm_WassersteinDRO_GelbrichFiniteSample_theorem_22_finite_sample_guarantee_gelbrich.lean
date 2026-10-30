-- Prove2me | Theorems.Thm_WassersteinDRO_GelbrichFiniteSample_theorem_22_finite_sample_guarantee_gelbrich
-- name    : WassersteinDRO.GelbrichFiniteSample.theorem_22_finite_sample_guarantee_gelbrich
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:03:04.805987+00:00
-- url     : https://prove2.me/theorems/00692520-1c74-4992-8e99-044f73819b6c
-- title:
--   Theorem 22 (29a): finite sample guarantee for the Gelbrich risk
-- statement:
--   This item is part (29a) of Theorem 22. Part (29b), the guarantee for an optimizer of the Gelbrich risk optimization problem (19), is not part of this item.
--
--   Let $m \in \mathbb N$, $\alpha > 2$, $A > 0$, $\mu \in \mathbb R^m$ and let $\Sigma$ be an $m \times m$ matrix. There is a constant $c > 1$, depending only on $m, \alpha, A, \mu, \Sigma$ (the constant of Theorem 21), with the following property.
--
--   Let $\mathbb P$ be any probability distribution on $\mathbb R^m$ with mean vector $\mu$, covariance matrix $\Sigma$ and $\mathbb E^{\mathbb P}[\exp(\|\xi\|_2^\alpha)] \le A$. Let $\Xi \subseteq \mathbb R^m$ be a closed set containing the support of $\mathbb P$, and let $\mathcal L$ be any set of measurable loss functions $\ell : \mathbb R^m \to [-\infty, +\infty]$. Let $\widehat\xi_1, \dots, \widehat\xi_N$ ($N \ge 1$) be drawn independently from $\mathbb P$, with sample mean $\widehat\mu$ and sample covariance matrix $\widehat\Sigma$ (normalized by $1/N$). Then for every $\eta \in (0, 1)$ and every $\varepsilon \ge \varepsilon_N(\eta) = \log(c/\eta)/\sqrt N$,
--
--   $$\mathbb P^N\Big\{ \mathcal R(\mathbb P, \ell) \le \overline{\mathcal R}_\varepsilon(\widehat\mu, \widehat\Sigma, \ell) \quad \forall \ell \in \mathcal L \Big\} \ge 1 - \eta,$$
--
--   where $\mathcal R(\mathbb P, \ell) = \mathbb E^{\mathbb P}[\ell(\xi)]$ is the true risk and $\overline{\mathcal R}_\varepsilon(\widehat\mu, \widehat\Sigma, \ell)$ is the Gelbrich risk, the worst-case risk over all distributions on $\Xi$ whose mean and covariance lie in $\mathcal U_\varepsilon(\widehat\mu, \widehat\Sigma)$.
--
--   The Gelbrich risk, computed from the first two sample moments alone, is thus an upper confidence bound on the true risk, simultaneously for all losses, with a radius of order $N^{-1/2}$ that does not deteriorate with the dimension.
--
--   **Formalization Note** The probability bound is stated as: some measurable set of samples contained in the event has $\mathbb P^N$-probability at least $1 - \eta$; the event quantifies over an arbitrary family $\mathcal L$ and need not be measurable. The universal quantifier over $\ell \in \mathcal L$ is inside the event.
--
--   Differences from the source:
--   - reading: P^N{R(P, ℓ) ≤ R̄ε(µ̂, Σ̂, ℓ) ∀ℓ ∈ L} ≥ 1 − η → some measurable set S inside the event has P^N(S) ≥ 1 − η (inner measure); reason: the event quantifies over an arbitrary L and need not be measurable; the inner-measure bound is never weaker than the outer-measure value and agrees with it on measurable events.
--   - encoding: c > 1 of Theorem 21, depending on P only through µ, Σ, α, A, and m → ∃ c with 1 < c placed after m, α, A, µ, Σ and before P, Ξ, L, N, η, ε; reason: quantifier order expresses exactly this dependence.
--   - generalization: losses ℓ ∈ L satisfying Assumption 1 (p. 9: upper semicontinuous and integrable under the nominal distribution P̂N) → every set L of measurable functions ℓ : ℝ^m → [−∞, +∞]; reason: the guarantee holds for every set of measurable losses and specializes to the paper's L; under Theorem 22 the nominal distribution is random, so Assumption 1 would be a sample-dependent condition.
--   - encoding: Ξ ⊆ R^m a closed set known to contain the support of P (p. 6) → IsClosed Ξ and P(Ξᶜ) = 0; reason: for closed Ξ, containing the support of P is the same as P(Ξᶜ) = 0.
--   - encoding: P has mean vector µ and covariance matrix Σ, E^P[exp(‖ξ‖₂^α)] ≤ A → HasMeanCov P µ Σ (with finite second moments) and ∫⁻ ofReal(exp(‖ξ‖^α)) dP ≤ ofReal A; reason: a covariance matrix presupposes finite second moments, which also follow from the moment bound; the lower Lebesgue integral of a positive function is its expectation.
--   - encoding: N independent training samples, εN(η) = log(c/η)/√N → N ≥ 1 samples in Fin N → ℝ^m under the product measure Measure.pi (fun _ => P); reason: the samples are indexed by i ∈ {1, …, N} and ε_N divides by √N.
-- source:
--   Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning, arXiv:1908.08729v2, Theorem 22 (Finite sample guarantees II), eq. (29a), p. 23; conditions of Theorem 21 and eq. (28), p. 23

import Mathlib
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_risk
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_HasMeanCov
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_sampleMean
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_sampleCov
import Definitions.Def_WassersteinDRO_GelbrichFiniteSample_gelbrichRisk

open MeasureTheory

namespace WassersteinDRO.GelbrichFiniteSample

/-- **Theorem 22 (29a): finite sample guarantee for the Gelbrich risk.**
Kuhn, Mohajerin Esfahani, Nguyen, Shafieezadeh-Abadeh, *Wasserstein Distributionally Robust Optimization: Theory and Applications in Machine Learning*, arXiv:1908.08729v2, Theorem 22 (Finite sample guarantees II), eq. (29a), p. 23: "Assume that all conditions of
Theorem 21 hold and ε_N(η) is defined as in (28). Then, for all η ∈ (0,1) and ε ≥ ε_N(η) we have
P^N{R(P, ℓ) ≤ R̄_ε(µ̂, Σ̂, ℓ) ∀ℓ ∈ L} ≥ 1 − η. (29a)" The conditions of Theorem 21 (p. 23): P has
mean vector µ and covariance matrix Σ, and E^P[exp(‖ξ‖₂^α)] ≤ A for some α > 2 and A > 0; c > 1
depends on P only through µ, Σ, α, A and m, and ε_N(η) = log(c/η)/√N (28).

This item is **part (29a) only**. Part (29b) of Theorem 22 (p. 24), the guarantee for an optimizer
ℓ⋆ of the Gelbrich risk optimization problem (19), is not formalized in this mission.

For every `m`, `α > 2`, `A > 0`, `µ` and `Σ` there is `c > 1` such that for every probability measure
`P` on `ℝ^m` with mean `µ`, covariance `Σ` and `∫ exp(‖ξ‖₂^α) dP ≤ A`, every closed `Ξ` with
`P(Ξᶜ) = 0`, every set `L` of measurable losses `ℓ : ℝ^m → [−∞, +∞]`, every `N ≥ 1`, `η ∈ (0, 1)` and
`ε ≥ log(c/η)/√N`: the event "`R(P, ℓ) ≤ R̄_ε(µ̂, Σ̂, ℓ)` for all `ℓ ∈ L`" (`µ̂, Σ̂` the sample mean and
covariance of `N` iid draws from `P`) contains a measurable set of `P^N`-probability at least `1 − η`.

**Formalization Note.** (1) The constant placement `∀ m α A µ Σ, ∃ c > 1, ∀ P Ξ L N η ε` encodes
"c depends on P only through µ, Σ, α, A, m"; it is Theorem 21's constant ("ε_N(η) is defined as in
(28)"). (2) `P^N{E} ≥ 1 − η` is an inner-measure bound (some measurable `S ⊆ E` has
`P^N(S) ≥ 1 − η`), because `E` quantifies over an arbitrary `L` and need not be measurable; this is
never weaker than the outer-measure value. (3) The quantifier `∀ ℓ ∈ L` is inside the event: one
event for all losses at once. (4) Assumption 1 (p. 9: every `ℓ ∈ L` upper semicontinuous and
integrable under the nominal distribution) is not assumed: the statement holds for every set of
measurable losses, which covers the paper's `L`. (5) `Ξ` is closed and contains the support of
`P` (p. 6), encoded as `IsClosed Ξ` and `P(Ξᶜ) = 0`. (6) `HasMeanCov` includes finite second
moments, implied for `P` by the moment condition, which is a `lintegral` (exact expectation of a
positive function). (7) `N ≥ 1`: the samples are indexed `1, …, N` and `ε_N` divides by `√N`. -/
theorem theorem_22_finite_sample_guarantee_gelbrich (m : ℕ) (α A : ℝ) (hα : 2 < α) (hA : 0 < A)
    (μ : EuclideanSpace ℝ (Fin m)) (Sig : Matrix (Fin m) (Fin m) ℝ) :
    ∃ c : ℝ, 1 < c ∧
      ∀ (P : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure P],
        HasMeanCov P μ Sig →
        ∫⁻ ξ, ENNReal.ofReal (Real.exp (‖ξ‖ ^ α)) ∂P ≤ ENNReal.ofReal A →
        ∀ (Ξ : Set (EuclideanSpace ℝ (Fin m))), IsClosed Ξ → P Ξᶜ = 0 →
        ∀ (L : Set (EuclideanSpace ℝ (Fin m) → EReal)), (∀ ℓ ∈ L, Measurable ℓ) →
        ∀ (N : ℕ), 0 < N → ∀ (η : ℝ), 0 < η → η < 1 →
        ∀ (ε : ℝ), Real.log (c / η) / Real.sqrt N ≤ ε →
        ∃ S : Set (Fin N → EuclideanSpace ℝ (Fin m)), MeasurableSet S ∧
          S ⊆ {ξh | ∀ ℓ ∈ L, risk P ℓ ≤ gelbrichRisk Ξ ε (sampleMean ξh) (sampleCov ξh) ℓ} ∧
          ENNReal.ofReal (1 - η) ≤ Measure.pi (fun _ : Fin N => P) S := by sorry

end WassersteinDRO.GelbrichFiniteSample
