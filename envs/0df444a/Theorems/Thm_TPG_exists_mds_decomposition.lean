-- Prove2me | Theorems.Thm_TPG_exists_mds_decomposition
-- name    : TPG.exists_mds_decomposition
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:58:27.10598+00:00
-- url     : https://prove2.me/theorems/f7ea1da9-0c83-47ec-b7e6-52da79f66a83
-- title:
--   Martingale-difference decomposition of the centered TPG sum with bounded, local increments
-- statement:
--   **Setting.** $S$ is a finite state space, actions are $Z_t\in\{0,1\}$, time is $t=0,1,\dots,T-1$ (the source's time $t+1$). The environment has transition matrices $P_z^t$, initial distribution $\rho$ and reward laws $R(\cdot\mid x,z)$ on $\mathbb R$ with $R([-M,M]\mid x,z)=1$. $\mathbb P_\theta$ is the law of the trajectory $(X_t,Z_t,Y_t)_{t<T}$ under the Bernoulli policy $\pi_\theta$, and $\mathcal F_a^b=\sigma\bigl((X_t,Z_t,Y_t):a\le t\le b\bigr)$.
--
--   Fix a truncation size $k\ge0$ and consider the experimental policy $\pi_{1/2}$. Let $w_t^{\mathrm{IPW}}=2(2Z_t-1)$ and $B_t=\sum_{i=\max(0,t-k)}^{t}w_i^{\mathrm{IPW}}Y_t$, so that $\sum_{t<T}B_t=T\,\widehat\tau_k$. **Assumption 1** holds for all times with one constant $\gamma\in(0,1)$.
--
--   **Lemma.** There is a constant $C\ge0$, depending only on the environment, $k$, $\gamma$ and $M$, such that for every horizon $T$ there are functions $D_0,D_1,\dots$ of the trajectory with:
--
--   1. **locality:** $D_j$ is measurable with respect to $\mathcal F_{\max(0,j-k-1)}^{\,j}$;
--   2. **boundedness:** $|D_j|\le C$ everywhere;
--   3. **martingale differences:** $\mathbb E_{1/2}[D_0]=0$ and $\mathbb E_{1/2}[D_{j+1}\mid\mathcal F_0^{\,j}]=0$ almost surely for every $j$;
--   4. **decomposition:** almost surely,
--
--   $$\sum_{j<T}D_j=\sum_{t<T}B_t-\mathbb E_{1/2}\Bigl[\sum_{t<T}B_t\Bigr].$$
--
--   The $D_j$ are versions of the increments $\mathbb E[S_T\mid\mathcal F_0^{\,j}]-\mathbb E[S_T\mid\mathcal F_0^{\,j-1}]$ of the Doob martingale of $S_T=\sum_tB_t$. Their uniform bound comes from the geometric forgetting of Assumption 1, and their locality from the Markov property. A martingale central limit theorem applied to $D_j/\sqrt T$ then gives the asymptotic normality of the estimator.
-- source:
--   Johari, Peng, Xing, Estimation of Treatment Effects Under Nonstationarity via the Truncated Policy Gradient Estimator, revised manuscript of October 2026 (revision of arXiv:2506.05308v3, https://arxiv.org/abs/2506.05308); numbering follows the revised manuscript. Auxiliary statement, not a numbered result of the paper: it is the martingale representation underlying the central limit theorem for temporally nonhomogeneous Markov chains (Lemma 6, p. 51, Arlotto and Steele 2016) that the proof of Lemma 3 in Appendix H.1, pp. 51–53, applies to the sum S_T = T τ̂_k; the paper cites that theorem instead of constructing the martingale.

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Inference

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace TPG
theorem exists_mds_decomposition {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (k : ℕ) (γ M : ℝ) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hmix : ∀ T : ℕ, E.Mixing T γ) (hM : E.RewardBound M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ, ∃ D : ℕ → Traj S T → ℝ,
      (∀ j : ℕ, Measurable[sigmaWindow T (j - (k + 1)) j] (D j))
        ∧ (∀ (j : ℕ) (ω : Traj S T), |D j ω| ≤ C)
        ∧ (∫ ω, D 0 ω ∂(E.expLaw T (1 / 2)) = 0)
        ∧ (∀ j : ℕ, (E.expLaw T (1 / 2))[D (j + 1) | sigmaWindow T 0 j]
              =ᵐ[E.expLaw T (1 / 2)] 0)
        ∧ (∀ᵐ ω ∂(E.expLaw T (1 / 2)),
            ∑ j ∈ Finset.range T, D j ω
              = (∑ t : Fin T, Bt k t ω) - ∫ ω', ∑ t : Fin T, Bt k t ω' ∂(E.expLaw T (1 / 2))) := by sorry
end TPG
