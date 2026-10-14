-- Prove2me | Theorems.Thm_TPG_variance_sum_window_le
-- name    : TPG.variance_sum_window_le
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:40:08.608323+00:00
-- url     : https://prove2.me/theorems/2db2de89-952d-44ad-b137-2b2c5448ce0b
-- title:
--   Variance of a sum of bounded functionals of short time windows is $O(T)$ under Assumption 1
-- statement:
--   **Setting.** $S$ is a finite state space, actions are $Z_t\in\{0,1\}$, time is $t=0,1,\dots,T-1$ (the source's time $t+1$). The environment has transition matrices $P_z^t$, initial distribution $\rho$ and reward laws $R(\cdot\mid x,z)$ on $\mathbb R$ with $R([-M,M]\mid x,z)=1$. $\mathbb P_\theta$ is the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ under the Bernoulli policy $\pi_\theta$, and $\mathcal F_a^b=\sigma\bigl((X_t,Z_t,Y_t):a\le t\le b\bigr)$.
--
--   **Assumption 1** holds on the horizon $T$ with a constant $\gamma\in(0,1)$: $\|f'P_z^t-fP_z^t\|_{\mathrm{TV}}\le\gamma\|f'-f\|_{\mathrm{TV}}$ for all $t<T$, all $z$ and all probability vectors $f,f'$.
--
--   **Lemma.** Let $0<\theta<1$, let $w\ge0$ be an integer and $K$ a real number, and for $j=0,\dots,T-1$ let $U_j$ be a real function of the trajectory that is measurable with respect to $\mathcal F_{\max(0,j-w)}^{\,j}$ and satisfies $|U_j|\le K$. Then
--
--   $$\operatorname{Var}_\theta\Bigl(\sum_{j<T}U_j\Bigr)\le T\,K^2\Bigl(2w+3+\frac{8}{1-\gamma}\Bigr).$$
--
--   Functionals of time windows separated by $h$ steps have covariance at most $4\gamma^{h-1}K^2$ by the strong mixing of the process and the covariance inequality, and summing over pairs gives a bound linear in the horizon. The lemma is the law-of-large-numbers input of the central limit theorem and of the variance-estimator consistency.
--
--   **Formalization Note** $j-w$ is a truncated subtraction of natural numbers.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it is the covariance-summation step used for the variance bound of Appendix F.1, pp. 40–41, and for the consistency proof of Appendix H.2, pp. 53–54, obtained from Lemma 1 and Lemma 2 (Appendix A.4, pp. 27–28).

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Inference

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem variance_sum_window_le {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (T w : ℕ) (θ γ M K : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hmix : E.Mixing T γ) (hM : E.RewardBound M)
    (U : ℕ → Traj S T → ℝ)
    (hU : ∀ j : ℕ, Measurable[sigmaWindow T (j - w) j] (U j))
    (hK : ∀ (j : ℕ) (ω : Traj S T), |U j ω| ≤ K) :
    variance (fun ω : Traj S T => ∑ j ∈ Finset.range T, U j ω) (E.expLaw T θ)
      ≤ (T : ℝ) * K ^ 2 * (2 * (w : ℝ) + 3 + 8 / (1 - γ)) := by sorry
end TPG
