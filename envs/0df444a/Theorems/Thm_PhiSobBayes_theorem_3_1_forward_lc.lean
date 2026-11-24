-- Prove2me | Theorems.Thm_PhiSobBayes_theorem_3_1_forward_lc
-- name    : PhiSobBayes.theorem_3_1_forward_lc
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-24T06:27:15.773994+00:00
-- url     : https://prove2.me/theorems/070f6a69-37ac-427d-ac6e-38c5b8bd2b95
-- title:
--   Theorem 3.1 (i)⇒(ii) for log-concave $\mu$: $R_\Phi(t,f)\ge \mathrm{Ent}^\Phi_\mu(f)/(1+Ct)$
-- statement:
--   This is the direction (i) $\Rightarrow$ (ii) of Theorem 3.1, in the setting of that theorem (log-concave prior).
--
--   Let $\mu(dx)=e^{-V(x)}dx$ be a log-concave probability measure on $\mathbb R^n$, let $C>0$, let $J\subseteq\mathbb R$ be an open interval and let $\Phi:J\to\mathbb R$ be smooth with $\Phi''>0$ and $1/\Phi''$ concave on $J$. Suppose $\mu$ satisfies the $\Phi$-Sobolev inequality with constant $C$:
--   $$\mathrm{Ent}^\Phi_\mu(g)\le\frac C2\,\mathbb E_\mu\big[\Phi''(g)\,\|\nabla g\|_2^2\big]\qquad\text{for all }g\in\mathcal A^J_0 .$$
--   Then for every test function $f\in\mathcal A^J_0$ and every signal-to-noise ratio $t>0$, the $\Phi$-Bayes risk of estimating $f(X)$ from $Y_t=\sqrt t\,X+G$ (with $X\sim\mu$, $G\sim\mathcal N(0,I_n)$ independent) satisfies
--   $$R_\Phi(t,f)\ \ge\ \frac{\mathrm{Ent}^\Phi_\mu(f)}{1+Ct}.$$
--
--   Together with the converse direction this characterizes the $\Phi$-Sobolev constant of a log-concave measure through Bayesian estimation lower bounds.
--
--   **Formalization Note** The risk `bayesRisk` is $[0,\infty]$-valued; the real lower bound is embedded with `ENNReal.ofReal`. Log-concavity is the standing hypothesis of Theorem 3.1 (`IsLogConcave μ`).
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Theorem 3.1, p.15 (PDF 15), direction (i) ⇒ (ii); proof in Section 6.1, pp.30–31 (PDF 30–31)

import Mathlib
import Definitions.Def_PhiSobBayes_IsOpenInterval
import Definitions.Def_PhiSobBayes_AdmissiblePhi
import Definitions.Def_PhiSobBayes_testClass
import Definitions.Def_PhiSobBayes_phiEnt
import Definitions.Def_PhiSobBayes_PhiSobolev
import Definitions.Def_PhiSobBayes_bayesRisk
import Definitions.Def_PhiSobBayes_IsLogConcave

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- **Theorem 3.1, direction (i) ⇒ (ii), for a log-concave prior.** If a log-concave probability
measure `μ` on `ℝⁿ` satisfies the Φ-Sobolev inequality with constant `C > 0`, then for every
`f ∈ A^J_0` and `t > 0`, `R_Φ(t, f) ≥ Ent^Φ_μ(f) / (1 + C t)`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Theorem 3.1, p.15 (PDF 15), direction (i) ⇒ (ii), under the standing hypothesis of Theorem 3.1 that `μ` is log-concave; proof in Section 6.1, pp.30–31 (PDF 30–31). -/
theorem theorem_3_1_forward_lc {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : IsLogConcave μ)
    (C : ℝ) (hC : 0 < C) (J : Set ℝ) (hJ : IsOpenInterval J) (Φ : ℝ → ℝ) (hΦ : AdmissiblePhi J Φ)
    (hS : PhiSobolev μ J Φ C) (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : f ∈ testClass n J)
    (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal (phiEnt μ Φ f / (1 + C * t)) ≤ bayesRisk μ J Φ t f := by sorry

end PhiSobBayes
