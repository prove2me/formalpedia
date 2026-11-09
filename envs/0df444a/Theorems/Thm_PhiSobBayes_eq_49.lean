-- Prove2me | Theorems.Thm_PhiSobBayes_eq_49
-- name    : PhiSobBayes.eq_49
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:08:31.566207+00:00
-- url     : https://prove2.me/theorems/6f64f4bf-97c5-434c-b80b-5d9967248490
-- title:
--   Section 6.1, (49) — $R_\Phi(t,f)\le\frac1{2t}\mathbb E_\mu[\Phi''(f)\|\nabla f\|_2^2]$ for log-concave $\mu$
-- statement:
--   Let $\mu$ be a log-concave probability measure on $\mathbb R^n$, $J$ an open interval and $\Phi:J\to\mathbb R$ smooth with $\Phi''>0$ and $1/\Phi''$ concave. For every $f\in\mathcal A^J_0$ and every $t>0$,
--   $$R_\Phi(t,f)\le\frac1{2t}\,\mathbb E_\mu\big[\Phi''(f)\,\|\nabla f\|_2^2\big].\tag{49}$$
--
--   This is the key inequality of the proof of Theorem 3.1. It gives the direction (ii) ⇒ (i) by letting $t\to\infty$, and the one-SNR clause directly.
--
--   Differences from the source:
--   - encoding: R_Φ(t, f) ≤ (1/(2t)) 𝔼_μ[Φ″(f)‖∇f‖²] as real numbers → bayesRisk (in [0, ∞]) ≤ ENNReal.ofReal of the right-hand side; reason: the risk is defined in [0, ∞]; the right-hand side is a nonnegative real
--   - reading: μ log-concave: μ(dx) = e^{−V(x)}dx with ∇²V ⪰ 0 (p.13) → V twice Fréchet differentiable with D²V(x)(v,v) ≥ 0; reason: the Hessian condition presupposes that the Hessian exists; no stronger regularity is asked
--   - encoding: Φ : J → ℝ → Φ : ℝ → ℝ with AdmissiblePhi J Φ; reason: Lean functions are total; only the values on J (and derivatives at points of the open J) enter
--   - encoding: ℝⁿ → EuclideanSpace ℝ (Fin n); reason: Lean's Euclidean space; same norm, Lebesgue measure and gradient
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Section 6.1, p.30 (PDF 30), display (49)

import Mathlib
import Definitions.Def_PhiSobBayes_IsOpenInterval
import Definitions.Def_PhiSobBayes_AdmissiblePhi
import Definitions.Def_PhiSobBayes_testClass
import Definitions.Def_PhiSobBayes_IsLogConcave
import Definitions.Def_PhiSobBayes_bayesRisk

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- **Section 6.1, the key inequality (49).** For log-concave `μ`, an open interval `J`, `Φ` as in
Theorem 3.1, `f ∈ A^J_0` and `t > 0`,
`R_Φ(t, f) ≤ (1/(2t)) 𝔼_μ[Φ″(f) ‖∇f‖₂²]`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Section 6.1 (proof of Theorem 3.1), p.30 (PDF 30), display (49). -/
theorem eq_49 {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : IsLogConcave μ) (J : Set ℝ)
    (hJ : IsOpenInterval J) (Φ : ℝ → ℝ) (hΦ : AdmissiblePhi J Φ) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : f ∈ testClass n J) (t : ℝ) (ht : 0 < t) :
    bayesRisk μ J Φ t f ≤
      ENNReal.ofReal (1 / (2 * t) * ∫ x, deriv (deriv Φ) (f x) * ‖gradient f x‖ ^ 2 ∂μ) := by sorry

end PhiSobBayes
