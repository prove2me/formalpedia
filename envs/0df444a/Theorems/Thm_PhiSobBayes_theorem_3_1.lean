-- Prove2me | Theorems.Thm_PhiSobBayes_theorem_3_1
-- name    : PhiSobBayes.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:08:40.809079+00:00
-- url     : https://prove2.me/theorems/d5ccb16a-cea5-4000-adba-200cfbd2fe8c
-- title:
--   Theorem 3.1 — for log-concave $\mu$, the $\Phi$-Sobolev inequality with constant $C$ holds iff $R_\Phi(t,f)\ge\mathrm{Ent}^\Phi_\mu(f)/(1+Ct)$ for all $f,t$
-- statement:
--   Fix a log-concave probability measure $\mu$ on $\mathbb R^n$ and $C>0$. Fix also an open interval $J$ and $\Phi:J\to\mathbb R$ smooth with $\Phi''>0$ and $1/\Phi''$ concave. Then the following are equivalent:
--
--   1. $\mu$ satisfies the $\Phi$-Sobolev inequality (1) with constant $C$;
--   2. for every $f\in\mathcal A^J_0$ and every $t>0$, in the Gaussian additive model $Y_t=\sqrt t\,X+G$,
--   $$R_\Phi(t,f)\ge\frac{\mathrm{Ent}^\Phi_\mu(f)}{1+Ct}.\tag{8}$$
--
--   More generally, if there are $b>0$ and $T>0$ such that $R_\Phi(T,f)\ge b\,\mathrm{Ent}^\Phi_\mu(f)$ for every $f\in\mathcal A^J_0$, then $\mu$ satisfies the $\Phi$-Sobolev inequality (1) with $C=\frac1{bT}$.
--
--   In words, the $\Phi$-optimal risk is at least a $(1+Ct)^{-1}$-fraction of the $\Phi$-trivial risk $\mathrm{Ent}^\Phi_\mu(f)$ exactly when the $\Phi$-Sobolev inequality holds. With $\Phi(z)=(z-1)^2$ this characterizes the Poincaré constant through the minimum mean-square error, and with $\Phi(z)=z\log z$ the log-Sobolev constant through the entropy loss.
--
--   **Formalization Note** The risk is $[0,\infty]$-valued and the real lower bounds are embedded by `ENNReal.ofReal`; this is faithful because $\mathrm{Ent}^\Phi_\mu(f)\ge0$ on $\mathcal A^J_0$. The statement is the conjunction of the equivalence and the one-SNR clause.
--
--   Differences from the source:
--   - reading: μ log-concave: μ(dx) = e^{−V(x)}dx with ∇²V ⪰ 0 (p.13) → V twice Fréchet differentiable with D²V(x)(v,v) ≥ 0; reason: the Hessian condition presupposes that the Hessian exists; no stronger regularity is asked
--   - encoding: Φ : J → ℝ → Φ : ℝ → ℝ, used only on J (estimators and test functions are J-valued); reason: Lean functions are total; values outside J never enter
--   - encoding: R_Φ(t, f) ≥ Ent^Φ_μ(f)/(1 + Ct) and R_Φ(T, f) ≥ b Ent^Φ_μ(f) as real inequalities → bayesRisk (in [0, ∞]) ≥ ENNReal.ofReal of the real bound; reason: the risk is defined in [0, ∞]; the bounds are nonnegative since Ent^Φ_μ(f) ≥ 0 on A^J_0
--   - encoding: ℝⁿ → EuclideanSpace ℝ (Fin n); reason: Lean's Euclidean space; same norm, Lebesgue measure and gradient
-- source:
--   Li–Zadik, Functional inequalities from the fundamental limits of Bayesian estimation, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Theorem 3.1, p.15 (PDF 15); informal Theorem 1.1, p.5 (PDF 5); proof Section 6.1, pp.30–31

import Mathlib
import Definitions.Def_PhiSobBayes_IsOpenInterval
import Definitions.Def_PhiSobBayes_AdmissiblePhi
import Definitions.Def_PhiSobBayes_testClass
import Definitions.Def_PhiSobBayes_phiEnt
import Definitions.Def_PhiSobBayes_PhiSobolev
import Definitions.Def_PhiSobBayes_IsLogConcave
import Definitions.Def_PhiSobBayes_bayesRisk

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

namespace PhiSobBayes

/-- **Theorem 3.1 (functional inequalities as Bayes-risk lower bounds).** Fix a log-concave `μ` on
`ℝⁿ` and `C > 0`, an open interval `J` and `Φ : J → ℝ` smooth with `Φ″ > 0` and `1/Φ″` concave.
Then the following are equivalent:
(i) `μ` satisfies the Φ-Sobolev inequality (1) with constant `C`;
(ii) for every `f ∈ A^J_0` and every `t > 0`, `R_Φ(t, f) ≥ Ent^Φ_μ(f)/(1 + Ct)` (8).
More generally, if `R_Φ(T, f) ≥ b Ent^Φ_μ(f)` for some `b > 0`, `T > 0` and every `f ∈ A^J_0`, then
`μ` satisfies (1) with `C = 1/(bT)`.

Li–Zadik, *Functional inequalities from the fundamental limits of Bayesian estimation*, STOC 2027 submission (held version, sha256 5ea05e95…8ed487), Theorem 3.1, p.15 (PDF 15); informal version Theorem 1.1, p.5; proof in Section 6.1,
pp.30–31.

**Formalization Note** The risk `R_Φ` is `[0, ∞]`-valued (`bayesRisk`), and the real lower bounds
are embedded by `ENNReal.ofReal`. This is faithful because `Ent^Φ_μ(f) ≥ 0` for `f ∈ A^J_0`
(Jensen). The second conjunct is the theorem's last sentence; it does not involve `C`. -/
theorem theorem_3_1 {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (hμ : IsLogConcave μ) (C : ℝ) (hC : 0 < C)
    (J : Set ℝ) (hJ : IsOpenInterval J) (Φ : ℝ → ℝ) (hΦ : AdmissiblePhi J Φ) :
    (PhiSobolev μ J Φ C ↔
      ∀ f ∈ testClass n J, ∀ t : ℝ, 0 < t →
        ENNReal.ofReal (phiEnt μ Φ f / (1 + C * t)) ≤ bayesRisk μ J Φ t f) ∧
    (∀ b T : ℝ, 0 < b → 0 < T →
      (∀ f ∈ testClass n J, ENNReal.ofReal (b * phiEnt μ Φ f) ≤ bayesRisk μ J Φ T f) →
      PhiSobolev μ J Φ (1 / (b * T))) := by sorry

end PhiSobBayes
