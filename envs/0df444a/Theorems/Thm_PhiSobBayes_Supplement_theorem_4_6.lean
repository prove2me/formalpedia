-- Prove2me | Theorems.Thm_PhiSobBayes_Supplement_theorem_4_6
-- name    : PhiSobBayes.Supplement.theorem_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:44:59.470198+00:00
-- url     : https://prove2.me/theorems/ef8d87b1-e1b3-4cb9-872b-1a1eb4e07f96
-- title:
--   Theorem 4.6 — Gaussian null model: $I(U;X\mid Y_s)\ge I(U;X)/10^3$ and $C_{\mathrm{LS}}(\mu)\le 10^3/s$
-- statement:
--   **Theorem 4.6** (Gaussian null model). Let $\mu$ be a log-concave probability measure on $\mathbb R^n$ and $X\sim\mu$, normalized as in Section 4.2: $\mathbb E X=0$ and
--
--   $$
--   \mathbb E\,e^{\langle u,X\rangle}\le e^{\|u\|_2^2/2}\qquad\text{for every }u\in\mathbb R^n. \tag{12}
--   $$
--
--   Let $t>0$ and write $\chi^2(Y_t\,\|\,\gamma_n)$ for the $\chi^2$-divergence between the law of the observation $Y_t=\sqrt t\,X+G$ at SNR $t$ and the pure-noise law $\gamma_n=N(0,I_n)$. Suppose
--
--   $$
--   \Delta_t=\log\bigl(1+\chi^2(Y_t\,\|\,\gamma_n)\bigr)<\infty,\qquad\text{and let}\qquad s=\frac{t}{1000\,(1+\Delta_t)}.
--   $$
--
--   Let $Y_s=\sqrt s\,X+G$, $G\sim N(0,I_n)$ independent of $X$, be the Gaussian additive observation of $X$ at SNR $s$. Then:
--
--   1. for every randomized binary label $U$ of $X$ (a label $U\in\{0,1\}$ with $\mathbb P(U=1\mid X)$ a measurable function of $X$ and $U-X-Y_s$ a Markov chain),
--   $$
--   I(U;X\mid Y_s)\ \ge\ \frac{I(U;X)}{10^3}; \tag{13}
--   $$
--   2. $\mu$ satisfies the log-Sobolev inequality with constant $10^3/s$, that is,
--   $$
--   C_{\mathrm{LS}}(\mu)\ \le\ \frac{10^3}{s}=\frac{10^6\,(1+\Delta_t)}{t}.
--   $$
--
--   The mutual informations are in nats and take values in $[0,\infty]$. The theorem reduces a log-Sobolev bound for $\mu$ to a bound on how far the observation at SNR $t$ is from pure noise; together with $\log(1+\chi^2(Y_t\|\gamma_n))\le nt^2$ it gives the paper's $C_{\mathrm{LS}}(\mu)\lesssim n^{1/2}$ (Corollary 4.7).
--
--   **Formalization Note** A randomized binary label is encoded by the measurable function $p(x)=\mathbb P(U=1\mid X=x)\in[0,1]$, and the mutual informations are those of the coordinates of the label joint law of $(U,X,Y_s)$. The $\chi^2$-divergence is the published $\Psi$-divergence with $\Psi(r)=(r-1)^2$, whose correction term vanishes since $\Psi'(1)=0$; finiteness of $\Delta_t$ is finiteness of the $[0,\infty]$-valued divergence. The moment generating function in (12) is a lower Lebesgue integral, so an infinite value is not read as $0$.
--
--   Differences from the source:
--   - encoding: every randomized binary label $U$ of $X$ → every measurable $p:\mathbb R^n\to[0,1]$, with $(U,X,Y_s)$ distributed by the label joint law; reason: the statement involves only the joint law of $(U,X,Y_s)$, and the laws of randomized binary labels are exactly $\mu(\mathrm dx)\,\mathrm{Bernoulli}(p(x))\,N(\sqrt s\,x,I_n)$.
--   - reading: $C_{\mathrm{LS}}(\mu)\lesssim\frac1t\bigl(1+\Delta_t\bigr)$ → $C_{\mathrm{LS}}(\mu)\le 10^3/s=10^6(1+\Delta_t)/t$; reason: the paper's proof (p.42) ends with exactly this bound, which implies the $\lesssim$ form.
--   - encoding: $\Delta_t=\log(1+\chi^2)<\infty$ → the $[0,\infty]$-valued $\chi^2$ is $\ne\infty$ and $\Delta_t$ is $\log(1+\chi^2)$ of its real value; reason: Lean convention; the same condition and the same number.
--   - encoding: $\chi^2(\zeta\|\eta)=\int(\mathrm d\zeta/\mathrm d\eta-1)^2\,\mathrm d\eta$ (Definition 11) → the published $\Psi$-divergence with $\Psi(r)=(r-1)^2$; reason: $\Psi'(1)=0$, so it is $\int(\mathrm d\zeta/\mathrm d\eta-1)^2\,\mathrm d\eta$, and the pair is absolutely continuous here.
--   - encoding: $\mathbb E e^{\langle u,X\rangle}$ in (12) and $\mathbb E X=0$ → a lower Lebesgue integral and the Bochner integral of the identity; reason: Lean convention; $X$ has a finite first moment under (12), so the Bochner integral is the mean.
--   - encoding: $\mathbb R^n$ and a probability measure → `EuclideanSpace ℝ (Fin n)`, with the probability-measure clause of log-concavity repeated as an instance; reason: Lean convention; same instances.
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Theorem 4.6, p.18 (PDF 18); standing assumption (12), p.18; proof Section 8.2, pp.41–42 (PDF 41–42)

import Mathlib
import Definitions.Def_PhiSobBayes_IsLogConcave
import Definitions.Def_PhiSobBayes_LogSobolev
import Definitions.Def_PhiSobBayes_phiDiv
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
import Definitions.Def_ThompsonTutorial_InfoRatio_condMutualInfo
import Definitions.Def_PhiSobBayes_Supplement_labelJoint
import Definitions.Def_PhiSobBayes_gamObs

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ThompsonTutorial.InfoRatio
open scoped ENNReal

namespace PhiSobBayes.Supplement

/-- **Theorem 4.6 (Gaussian null model).** Let `μ` be a log-concave probability measure on `ℝⁿ` with
`𝔼X = 0` and `𝔼 e^{⟨u,X⟩} ≤ e^{‖u‖²/2}` for every `u` (the Section 4.2 standing assumption (12)). Let
`t > 0`, suppose `Δ_t = log(1 + χ²(Y_t ‖ γ_n)) < ∞`, and let `s = t/(1000(1 + Δ_t))`. Then every
randomized binary label `U` of `X` satisfies `I(U; X | Y_s) ≥ I(U; X)/10³` (13), and
`C_LS(μ) ≤ 10³/s = 10⁶(1 + Δ_t)/t`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027
submission (held version, sha256 5ea05e95…8ed487), Theorem 4.6, p.18 (PDF 18); standing assumption
(12), p.18; proof Section 8.2, pp.41–42, whose last line gives `C_LS(μ) ≤ 10³/s`.

**Formalization Note**
* `χ²(Y_t ‖ γ_n)` is `phiDiv (fun r => (r − 1)²) (gamObs μ t) γ_n` (Definition 11; `Ψ′(1) = 0`), in
  `[0, ∞]`; `Δ_t < ∞` is `χ² ≠ ∞`, and then `Δ_t = log(1 + χ².toReal)`.
* A randomized binary label is a measurable `p : ℝⁿ → [0, 1]` (`p(x) = ℙ(U = 1 | X = x)`), and the
  mutual informations are those of the coordinates of `labelJoint μ p s` (law of `(U, X, Y_s)`), in
  `[0, ∞]` (nats).
* `[IsProbabilityMeasure μ]` repeats the first clause of `IsLogConcave μ` as an instance.
* The `MGF` in (12) is a lower Lebesgue integral, so an infinite MGF is not read as `0`.
* The "in particular" `≲` is stated with the proof's constant: `LogSobolev μ (10³/s)`. -/
theorem theorem_4_6 {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ : IsLogConcave μ) (hmean : ∫ x, x ∂μ = 0)
    (hmgf : ∀ u : EuclideanSpace ℝ (Fin n),
      ∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ u x)) ∂μ ≤ ENNReal.ofReal (Real.exp (‖u‖ ^ 2 / 2)))
    (t : ℝ) (ht : 0 < t)
    (hχ : phiDiv (fun r => (r - 1) ^ 2) (gamObs μ t) (stdGaussian (EuclideanSpace ℝ (Fin n))) ≠ ∞) :
    let Δ := Real.log (1 + (phiDiv (fun r => (r - 1) ^ 2) (gamObs μ t)
      (stdGaussian (EuclideanSpace ℝ (Fin n)))).toReal)
    let s := t / (1000 * (1 + Δ))
    (∀ p : EuclideanSpace ℝ (Fin n) → ℝ, Measurable p → (∀ x, 0 ≤ p x ∧ p x ≤ 1) →
      mutualInfo (labelJoint μ p s) (fun ω => ω.1) (fun ω => ω.2.1) / 1000 ≤
        condMutualInfo (labelJoint μ p s) (fun ω => ω.1) (fun ω => ω.2.1) (fun ω => ω.2.2)) ∧
    LogSobolev μ (10 ^ 3 / s) := by sorry

end PhiSobBayes.Supplement
