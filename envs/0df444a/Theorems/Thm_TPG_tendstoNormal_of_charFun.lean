-- Prove2me | Theorems.Thm_TPG_tendstoNormal_of_charFun
-- name    : TPG.tendstoNormal_of_charFun
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:40:29.953334+00:00
-- url     : https://prove2.me/theorems/24bff772-6824-4555-9ae0-459493689121
-- title:
--   Lévy continuity for statistics of trajectories of growing length: convergence of characteristic functions gives convergence to $\mathcal N(0,v)$
-- statement:
--   For each horizon $T$ let $W_T$ be a measurable real statistic of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ generated under the experimental policy $\pi_{1/2}$ in an environment of `TPG_Model`, and let $v\ge0$.
--
--   **Lemma.** If for every real $t$
--
--   $$\mathbb E\bigl[e^{\,i\,t\,W_T}\bigr]\ \longrightarrow\ e^{-v t^2/2}\qquad(T\to\infty),$$
--
--   then $W_T$ converges in distribution to $\mathcal N(0,v)$: for every bounded continuous $f:\mathbb R\to\mathbb R$, $\mathbb E[f(W_T)]\to\int f\,d\mathcal N(0,v)$.
--
--   This is Lévy's continuity theorem for the laws of the $W_T$; it turns a characteristic-function estimate into the mode of convergence used in the statements of Lemma 3 and Theorem 2.
--
--   **Formalization Note** The expectation for each $T$ is taken under the horizon-$T$ trajectory law, so the statistics for different $T$ are defined on different probability spaces.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it is the standard continuity theorem used implicitly in the proof of Lemma 3, Appendix H.1, pp. 51–53, adapted to the convention that the statistic at horizon T lives on the horizon-T trajectory space.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Inference

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem tendstoNormal_of_charFun {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (W : (T : ℕ) → Traj S T → ℝ) (hW : ∀ T : ℕ, Measurable (W T))
    (v : ℝ) (hv : 0 ≤ v)
    (h : ∀ t : ℝ, Filter.Tendsto
      (fun T : ℕ => ∫ ω, Complex.exp (Complex.I * (t : ℂ) * (W T ω : ℂ)) ∂(E.expLaw T (1 / 2)))
      Filter.atTop (nhds (Complex.exp (-((v : ℂ) * (t : ℂ) ^ 2) / 2)))) :
    E.TendstoNormal W v := by sorry
end TPG
