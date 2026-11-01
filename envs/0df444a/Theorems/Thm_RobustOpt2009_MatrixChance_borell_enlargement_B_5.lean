-- Prove2me | Theorems.Thm_RobustOpt2009_MatrixChance_borell_enlargement_B_5
-- name    : RobustOpt2009.MatrixChance.borell_enlargement_B_5
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-31T06:14:28.748007+00:00
-- url     : https://prove2.me/theorems/1135abd6-83d7-460b-88a7-afb497f900ad
-- title:
--   Fact (!) in the proof of Theorem B.5.1 — Borell's Gaussian enlargement inequality
-- statement:
--   This is the Gaussian enlargement inequality of C. Borell, stated as fact (!) in the proof of Theorem B.5.1.
--
--   Let $\gamma_m=N(0,I_m)$ be the standard Gaussian measure on $\mathbb R^m$. Let $X\subseteq\mathbb R^m$ be a closed set, and let $\alpha>0$ and $\varepsilon\ge0$ be reals with $\gamma_m(X)\ge\alpha$. Write $\operatorname{dist}(x,X)=\inf_{y\in X}\|x-y\|_2$. Then
--   $$
--   \gamma_m\{x:\operatorname{dist}(x,X)>\varepsilon\}\le T\big(q(1-\alpha)+\varepsilon\big).
--   $$
--   Here $T(t)=\Pr\{G>t\}$, with $G\sim N(0,1)$, is the book's upper-tail function $\operatorname{Erf}$, and $q=\operatorname{ErfInv}$ is its quantile.
--
--   In the source this fact immediately yields Theorem B.5.1(ii) and the general-covariance bound (B.5.4). It is the sharp Gaussian isoperimetric inequality (Borell; Sudakov–Tsirelson), $\gamma_m(X_\varepsilon)\ge\Phi(\Phi^{-1}(\gamma_m(X))+\varepsilon)$, written in upper-tail form.
--
--   **Formalization Note** As in the mission's setting file, $T$ and $q$ are defined on extended reals: $q(p)=\inf\{t\in\overline{\mathbb R}:T(t)\le p\}$, with $q(0)=+\infty$ and $T(+\infty)=0$. At $\alpha=1$ the bound therefore asserts that the event has probability zero. This holds because a closed set of full Gaussian measure is the whole space. The distance is Mathlib's `Metric.infDist` on `EuclideanSpace ℝ (Fin m)`, and probabilities are real values of the measure.
-- source:
--   Ben-Tal, El Ghaoui and Nemirovski, Robust Optimization, Princeton University Press, 2009, https://doi.org/10.1515/9781400831050, Appendix B.5.1, proof of Theorem B.5.1, statement (!) attributed to C. Borell [31] (printed p. 508–509; p. 506 of the 2021 online version https://www2.isye.gatech.edu/~nemirovs/ROBook.pdf).

import Definitions.Def_RobustOpt2009_MatrixChance_Setting

open MeasureTheory ProbabilityTheory

namespace RobustOpt2009.MatrixChance

theorem borell_enlargement_B_5 {m : ℕ} (X : Set (EuclideanSpace ℝ (Fin m))) (α ε : ℝ)
    (hX : IsClosed X) (hα : 0 < α) (hε : 0 ≤ ε)
    (hprob : α ≤ ((stdGaussian (EuclideanSpace ℝ (Fin m))) X).toReal) :
    ((stdGaussian (EuclideanSpace ℝ (Fin m))) {x | ε < Metric.infDist x X}).toReal ≤
      normalTail (tailQuantile (1 - α) + (ε : EReal)) := by sorry

end RobustOpt2009.MatrixChance
