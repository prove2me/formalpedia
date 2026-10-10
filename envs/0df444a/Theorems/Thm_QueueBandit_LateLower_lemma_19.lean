-- Prove2me | Theorems.Thm_QueueBandit_LateLower_lemma_19
-- name    : QueueBandit.LateLower.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:39:59.532532+00:00
-- url     : https://prove2.me/theorems/94217d9e-abc2-4236-8626-59569f5a6750
-- title:
--   Lemma 19, p. 37 — α-consistent policies schedule each suboptimal link pair Ω(log t) times
-- statement:
--   Let $(\lambda,\mu)$ be an instance of a switch with $1\le U\le K$ queues and servers, $K\ge2$, satisfying Assumption 1 with optimal matching $k^*$, and let $T_{uk}(t+1)=\sum_{s=1}^t\mathbf 1\{\kappa_u(s)=k\}$.
--
--   For every $\alpha\in(0,1)$ and every $\alpha$-consistent policy there exist constants $\tau$ and $C>0$ such that for every queue $u$, every server $k\neq k^*_u$ and every $t>\tau$,
--   $$\mathbb E[T_{uk}(t+1)]+\sum_{u'\neq u}\mathbf 1\{k^*_{u'}=k\}\,\mathbb E[T_{u'k^*_u}(t+1)]\;\ge\;\frac{1}{\mathrm{KL}\big(\mu_{\min},\frac{\mu^*+1}{2}\big)}\Big((1-\alpha)\log t-\log(4KC)\Big).$$
--
--   The left side counts the schedules that a policy must spend to distinguish $\mu$ from the instance in which the best servers of $u$ and of the queue $u'$ owning server $k$ are swapped. This is the multi-queue analogue of the Lai–Robbins count lower bound and feeds Corollary 20.
--
--   **Formalization Note** The constants $\tau\in\mathbb N$ and $C$ are chosen after the instance and the policy, as printed; $C>0$ is added so that $\log(4KC)$ is meaningful (it can always be arranged). The factor $1/\mathrm{KL}$ is $0$ when $\mu^*=1$, where the divergence is $+\infty$. The arrival rates do not enter: the schedule never observes arrivals, so the expected counts depend on $\mu$ only. $K\ge2$ is added (for $K=1$ there is no $k\ne k^*_u$ and the statement is empty).
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 37, Lemma 19; proof pp. 38–39

import Mathlib
import Definitions.Def_QueueBandit_LateLower_Instance
import Definitions.Def_QueueBandit_LateLower_Dynamics

open MeasureTheory Finset Filter

namespace QueueBandit.LateLower

/-- Lemma 19 (p. 37). For an α-consistent policy there are constants τ and C > 0 such that for
every queue u, every server k ≠ k*_u and every t > τ,
E[T_uk(t+1)] + Σ_{u' ≠ u} 1{k*_{u'} = k} E[T_{u' k*_u}(t+1)]
  ≥ (1/KL(μ_min, (μ*+1)/2)) ((1 − α) log t − log(4KC)). -/
theorem lemma_19 {U K : ℕ} (hU : 0 < U) (hUK : U ≤ K) (hK : 2 ≤ K)
    (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hmu : ∀ u k, 0 ≤ mu u k ∧ mu u k ≤ 1) (hA1 : Assumption1 mu kstar)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (π : Policy U K) (hπ : IsAlphaConsistent π α) :
    ∃ τ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ u : Fin U, ∀ k : Fin K, k ≠ kstar u → ∀ t : ℕ, τ < t →
      invKL mu * ((1 - α) * Real.log t - Real.log (4 * K * C)) ≤
        expCount π mu u k t +
          ∑ u' ∈ univ.erase u, (if kstar u' = k then expCount π mu u' (kstar u) t else 0) := by sorry

end QueueBandit.LateLower
