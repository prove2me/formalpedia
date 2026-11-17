-- Prove2me | Theorems.Thm_PhiSobBayes_Supplement_theorem_4_9
-- name    : PhiSobBayes.Supplement.theorem_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:45:43.882926+00:00
-- url     : https://prove2.me/theorems/1f39fe63-75c9-4a67-b075-88f909aae259
-- title:
--   Theorem 4.9 — null-posterior model: $I(U;X\mid Y_s)\ge I(U;X)/10^3$ and $C_{\mathrm{LS}}(\mu)\le 10^3/s$
-- statement:
--   **Theorem 4.9** (null-posterior model). Let $\mu$ be a log-concave probability measure on $\mathbb R^n$ and $X\sim\mu$, normalized as in Section 4.2: $\mathbb E X=0$ and
--
--   $$
--   \mathbb E\,e^{\langle u,X\rangle}\le e^{\|u\|_2^2/2}\qquad\text{for every }u\in\mathbb R^n. \tag{12}
--   $$
--
--   Let $t>0$ and write $\chi^2(\mu\,\|\,\nu_t)$ for the $\chi^2$-divergence between the prior $\mu$ and the null-posterior prior $\nu_t=\int\mu_{t,y}\,\gamma_n(\mathrm dy)$ of display (6), the average over $y\sim\gamma_n$ of the posteriors $\mu_{t,y}$ at SNR $t$. Suppose
--
--   $$
--   \Delta'_t=\log\bigl(1+\chi^2(\mu\,\|\,\nu_t)\bigr)<\infty,\qquad\text{and let}\qquad s=\frac{t}{1000\,(1+\Delta'_t)}.
--   $$
--
--   Let $Y_s=\sqrt s\,X+G$, $G\sim N(0,I_n)$ independent of $X$, be the Gaussian additive observation of $X$ at SNR $s$. Then:
--
--   1. for every randomized binary label $U$ of $X$ (a label $U\in\{0,1\}$ with $\mathbb P(U=1\mid X)$ a measurable function of $X$ and $U-X-Y_s$ a Markov chain),
--   $$
--   I(U;X\mid Y_s)\ \ge\ \frac{I(U;X)}{10^3}; \tag{15}
--   $$
--   2. $\mu$ satisfies the log-Sobolev inequality with constant $10^3/s$, that is,
--   $$
--   C_{\mathrm{LS}}(\mu)\ \le\ \frac{10^3}{s}=\frac{10^6\,(1+\Delta'_t)}{t}.
--   $$
--
--   The mutual informations are in nats and take values in $[0,\infty]$. Since $\chi^2(\mu\|\nu_t)\le\chi^2(Y_t\|\gamma_n)$, the theorem is at least as strong as Theorem 4.6; together with $\log(1+\chi^2(\mu\|\nu_t))\lesssim nt^3$ it gives the paper's $C_{\mathrm{LS}}(\mu)\lesssim n^{1/3}$ (Corollary 4.10).
--
--   **Formalization Note** A randomized binary label is encoded by the measurable function $p(x)=\mathbb P(U=1\mid X=x)\in[0,1]$, and the mutual informations are those of the coordinates of the label joint law of $(U,X,Y_s)$. The $\chi^2$-divergence is the published $\Psi$-divergence with $\Psi(r)=(r-1)^2$, whose correction term vanishes since $\Psi'(1)=0$; finiteness of $\Delta'_t$ is finiteness of the $[0,\infty]$-valued divergence. The moment generating function in (12) is a lower Lebesgue integral, so an infinite value is not read as $0$.
--
--   Differences from the source:
--   - encoding: every randomized binary label $U$ of $X$ → every measurable $p:\mathbb R^n\to[0,1]$, with $(U,X,Y_s)$ distributed by the label joint law; reason: the statement involves only the joint law of $(U,X,Y_s)$, and the laws of randomized binary labels are exactly $\mu(\mathrm dx)\,\mathrm{Bernoulli}(p(x))\,N(\sqrt s\,x,I_n)$.
--   - reading: $C_{\mathrm{LS}}(\mu)\lesssim\frac1t\bigl(1+\Delta'_t\bigr)$ → $C_{\mathrm{LS}}(\mu)\le 10^3/s=10^6(1+\Delta'_t)/t$; reason: the paper's proof (p.44) ends with exactly this bound, which implies the $\lesssim$ form.
--   - encoding: $\Delta'_t=\log(1+\chi^2)<\infty$ → the $[0,\infty]$-valued $\chi^2$ is $\ne\infty$ and $\Delta'_t$ is $\log(1+\chi^2)$ of its real value; reason: Lean convention; the same condition and the same number.
--   - encoding: $\chi^2(\zeta\|\eta)=\int(\mathrm d\zeta/\mathrm d\eta-1)^2\,\mathrm d\eta$ (Definition 11) → the published $\Psi$-divergence with $\Psi(r)=(r-1)^2$; reason: $\Psi'(1)=0$, so it is $\int(\mathrm d\zeta/\mathrm d\eta-1)^2\,\mathrm d\eta$, and the pair is absolutely continuous here.
--   - encoding: $\mathbb E e^{\langle u,X\rangle}$ in (12) and $\mathbb E X=0$ → a lower Lebesgue integral and the Bochner integral of the identity; reason: Lean convention; $X$ has a finite first moment under (12), so the Bochner integral is the mean.
--   - encoding: $\mathbb R^n$ and a probability measure → `EuclideanSpace ℝ (Fin n)`, with the probability-measure clause of log-concavity repeated as an instance; reason: Lean convention; same instances.
--   - encoding: $\nu_t=\int\mu_{t,y}\,\gamma_n(\mathrm dy)$ (6) → $\mu$ with the averaged posterior density; reason: equal to (6) on every measurable set by Tonelli's theorem (proved in the verification file).
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Theorem 4.9, p.19 (PDF 19); standing assumption (12), p.18; display (6), p.11; proof Section 9.2, p.44 (PDF 44)

import Mathlib
import Definitions.Def_PhiSobBayes_IsLogConcave
import Definitions.Def_PhiSobBayes_LogSobolev
import Definitions.Def_PhiSobBayes_phiDiv
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo
import Definitions.Def_ThompsonTutorial_InfoRatio_condMutualInfo
import Definitions.Def_PhiSobBayes_Supplement_labelJoint
import Definitions.Def_PhiSobBayes_Supplement_nullPrior

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ThompsonTutorial.InfoRatio
open scoped ENNReal

namespace PhiSobBayes.Supplement

/-- **Theorem 4.9 (null-posterior model).** Let `μ` be a log-concave probability measure on `ℝⁿ` with
`𝔼X = 0` and `𝔼 e^{⟨u,X⟩} ≤ e^{‖u‖²/2}` for every `u` (the Section 4.2 standing assumption (12)). Let
`t > 0`, suppose `Δ′_t = log(1 + χ²(μ ‖ ν_t)) < ∞`, where `ν_t = 𝔼_{y∼γ_n} μ_{t,y}` (6), and fix
`s = t/(1000(1 + Δ′_t))`. Then every randomized binary label `U` of `X` satisfies
`I(U; X | Y_s) ≥ I(U; X)/10³` (15), and `C_LS(μ) ≤ 10³/s = 10⁶(1 + Δ′_t)/t`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027
submission (held version, sha256 5ea05e95…8ed487), Theorem 4.9, p.19 (PDF 19); standing assumption
(12), p.18; proof Section 9.2, p.44, whose last line gives `C_LS(μ) ≤ 10³/s`.

**Formalization Note**
* `χ²(μ ‖ ν_t)` is `phiDiv (fun r => (r − 1)²) μ (nullPrior μ t)` (Definition 11; `Ψ′(1) = 0`), in
  `[0, ∞]`; `Δ′_t < ∞` is `χ² ≠ ∞`, and then `Δ′_t = log(1 + χ².toReal)`.
* A randomized binary label is a measurable `p : ℝⁿ → [0, 1]`, and the mutual informations are those
  of the coordinates of `labelJoint μ p s` (law of `(U, X, Y_s)` under the planted model with prior
  `μ` at SNR `s`), in `[0, ∞]` (nats).
* `[IsProbabilityMeasure μ]` repeats the first clause of `IsLogConcave μ` as an instance.
* The `MGF` in (12) is a lower Lebesgue integral.
* The "in particular" `≲` is stated with the proof's constant: `LogSobolev μ (10³/s)`. -/
theorem theorem_4_9 {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ : IsLogConcave μ) (hmean : ∫ x, x ∂μ = 0)
    (hmgf : ∀ u : EuclideanSpace ℝ (Fin n),
      ∫⁻ x, ENNReal.ofReal (Real.exp (inner ℝ u x)) ∂μ ≤ ENNReal.ofReal (Real.exp (‖u‖ ^ 2 / 2)))
    (t : ℝ) (ht : 0 < t)
    (hχ : phiDiv (fun r => (r - 1) ^ 2) μ (nullPrior μ t) ≠ ∞) :
    let Δ' := Real.log (1 + (phiDiv (fun r => (r - 1) ^ 2) μ (nullPrior μ t)).toReal)
    let s := t / (1000 * (1 + Δ'))
    (∀ p : EuclideanSpace ℝ (Fin n) → ℝ, Measurable p → (∀ x, 0 ≤ p x ∧ p x ≤ 1) →
      mutualInfo (labelJoint μ p s) (fun ω => ω.1) (fun ω => ω.2.1) / 1000 ≤
        condMutualInfo (labelJoint μ p s) (fun ω => ω.1) (fun ω => ω.2.1) (fun ω => ω.2.2)) ∧
    LogSobolev μ (10 ^ 3 / s) := by sorry

end PhiSobBayes.Supplement
