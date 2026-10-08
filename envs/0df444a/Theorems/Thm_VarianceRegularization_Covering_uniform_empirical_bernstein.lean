-- Prove2me | Theorems.Thm_VarianceRegularization_Covering_uniform_empirical_bernstein
-- name    : VarianceRegularization.Covering.uniform_empirical_bernstein
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T19:41:21.186882+00:00
-- url     : https://prove2.me/theorems/1c08adb2-1eb0-4680-bfb0-33154fc35be8
-- title:
--   Lemma C.1 (Maurer–Pontil, Thm 6) — uniform empirical Bernstein bound via ℓ∞ covering numbers
-- statement:
--   Let $\mathcal F$ be a class of measurable functions $f : \mathcal X \to [M_0, M_1]$, $M = M_1 - M_0$, and let $X_1, \dots, X_n$ be i.i.d. with law $P$, $n \ge 1$. Write $\mathbb E[f] = \int f\,dP$, $\mathbb E_{\widehat P_n}[f] = \frac1n\sum_i f(X_i)$ and $\mathrm{Var}_{\widehat P_n}(f) = \frac1n \sum_i f(X_i)^2 - (\mathbb E_{\widehat P_n}[f])^2$. Let $N_\infty(\mathcal F, \epsilon, 2n)$ be the empirical $\ell_\infty$ covering number. If $n \ge 8M^2/t$, $t \ge \log 12$ and $\epsilon > 0$, then with probability at least $1 - 6 N_\infty(\mathcal F, \epsilon, 2n) e^{-t}$,
--   $$
--   \mathbb E[f] \le \mathbb E_{\widehat P_n}[f] + 3\sqrt{\frac{2\,\mathrm{Var}_{\widehat P_n}(f)\, t}{n}} + \frac{15 M t}{n} + 2\left(1 + 2\sqrt{\frac{2t}{n}}\right)\epsilon \qquad \text{for all } f \in \mathcal F.
--   $$
--
--   This is a uniform empirical Bernstein inequality: the deviation of the population mean from the sample mean is controlled by the *sample* standard deviation, uniformly over a class of finite empirical covering number. It is the first step of the proof of Theorem 3.
--
--   **Formalization Note** The sample is the coordinate process of the product measure $P^{\otimes n}$. The statement bounds the probability of the bad event (some $f \in \mathcal F$ violates the inequality) by $6 N_\infty e^{-t}$; this event need not be measurable, and its measure is the outer measure, as usual in empirical-process theory. The bound is computed in $[0, \infty]$, so an infinite covering number gives the trivial bound. The lemma is the paper's restatement of Maurer and Pontil (2009), Theorem 6 (with a general radius $\epsilon$ and $1/n$-normalized variance) and is formalized as printed in the paper.
-- source:
--   Duchi and Namkoong, Variance-based regularization with convex objectives, arXiv:1610.02581v3 (2017), p. 37, Lemma C.1, inequality (36) (citing Maurer and Pontil, Empirical Bernstein bounds and sample variance penalization, COLT 2009, Theorem 6)

import Mathlib
import Definitions.Def_VarianceRegularization_Covering_robustSup
import Definitions.Def_VarianceRegularization_Covering_empCoveringNumber

open MeasureTheory

namespace VarianceRegularization.Covering

/-- Lemma C.1 (Maurer and Pontil, Theorem 6, as restated in Duchi–Namkoong,
arXiv:1610.02581v3, p. 37): let `F` be a class of measurable functions `X → [M₀, M₁]`,
`M = M₁ - M₀`, `X₁,…,Xₙ` i.i.d. with law `P`, `n ≥ 8M²/t`, `t ≥ log 12`, `ε > 0`. With
probability at least `1 - 6 N∞(F, ε, 2n) e^{-t}`, for all `f ∈ F`,
`E[f] ≤ E_{P̂ₙ}[f] + 3√(2 Var_{P̂ₙ}(f) t / n) + 15Mt/n + 2(1 + 2√(2t/n)) ε`.
Stated as: the event where some `f ∈ F` violates (36) has (outer) measure at most
`6 N∞(F, ε, 2n) e^{-t}`, computed in `ℝ≥0∞` so that `N∞ = ∞` gives the trivial bound. -/
theorem uniform_empirical_bernstein {X : Type*} [MeasurableSpace X] (P : Measure X)
    [IsProbabilityMeasure P] (F : Set (X → ℝ)) (M0 M1 : ℝ) (hM : M0 ≤ M1)
    (hF : ∀ f ∈ F, Measurable f ∧ ∀ x, f x ∈ Set.Icc M0 M1) (n : ℕ) (hn : 0 < n) (t ε : ℝ)
    (hnt : 8 * (M1 - M0) ^ 2 / t ≤ n) (ht : Real.log 12 ≤ t) (hε : 0 < ε) :
    Measure.pi (fun _ : Fin n => P)
        {s | ∃ f ∈ F, empMean f s + 3 * Real.sqrt (2 * empVar f s * t / n)
          + 15 * (M1 - M0) * t / n + 2 * (1 + 2 * Real.sqrt (2 * t / n)) * ε < ∫ x, f x ∂P}
      ≤ 6 * (empCoveringNumber F ε (2 * n) : ENNReal) * ENNReal.ofReal (Real.exp (-t)) := by sorry

end VarianceRegularization.Covering
