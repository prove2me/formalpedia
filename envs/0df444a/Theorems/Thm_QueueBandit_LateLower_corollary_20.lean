-- Prove2me | Theorems.Thm_QueueBandit_LateLower_corollary_20
-- name    : QueueBandit.LateLower.corollary_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T22:40:16.027018+00:00
-- url     : https://prove2.me/theorems/022bd12b-29fc-4529-9015-2a84712afd95
-- title:
--   Corollary 20, p. 39 — summed Ω(log t) bounds on suboptimal schedules: total, per queue, and on servers optimal for no queue
-- statement:
--   Let $(\lambda,\mu)$ be an instance with $1\le U\le K$, $K\ge2$, satisfying Assumption 1, and let $D(\mu)=\Delta/\mathrm{KL}(\mu_{\min},(\mu^*+1)/2)$ as in display (2). For every $\alpha\in(0,1)$ and every $\alpha$-consistent policy there exist constants $\tau$ and $C>0$ such that for every $t>\tau$, writing $B(t)=(1-\alpha)\log t-\log(4KC)$:
--
--   1. $$2\Delta\sum_{u\in[U]}\sum_{k\neq k^*_u}\mathbb E[T_{uk}(t+1)]\ge U(K-1)\,D(\mu)\,B(t);$$
--   2. for every queue $u$, $$2\Delta\sum_{k\neq k^*_u}\mathbb E[T_{uk}(t+1)]\ge (U-1)\,D(\mu)\,B(t);$$
--   3. for every queue $u$, $$\Delta\sum_{k\notin k^*([U])}\mathbb E[T_{uk}(t+1)]\ge (K-U)\,D(\mu)\,B(t),$$ where the sum runs over the $K-U$ servers that are optimal for no queue.
--
--   These are the forms in which the count lower bound of Lemma 19 enters the queue-regret lower bound of Theorem 3: part 1 for the average regret, parts 2 and 3 for a single queue.
--
--   **Formalization Note** One pair $(\tau,C)$ serves all three parts, as printed. The paper's $\sum_{k>U}$ assumes the optimal servers are relabelled as $1,\dots,U$; the statement sums over the servers outside the range of $k^*$ instead. $C>0$ and $K\ge2$ are added as in Lemma 19; $D(\mu)=0$ when $\mu^*=1$.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 39, Corollary 20; proof pp. 40–41

import Mathlib
import Definitions.Def_QueueBandit_LateLower_Instance
import Definitions.Def_QueueBandit_LateLower_Dynamics

open MeasureTheory Finset Filter

namespace QueueBandit.LateLower

/-- Corollary 20 (p. 39). For an α-consistent policy there are constants τ and C > 0 such that
for every t > τ, with B(t) = (1 − α) log t − log(4KC):
(a) 2Δ Σ_u Σ_{k ≠ k*_u} E[T_uk(t+1)] ≥ U(K − 1) D(μ) B(t);
(b) for every u, 2Δ Σ_{k ≠ k*_u} E[T_uk(t+1)] ≥ (U − 1) D(μ) B(t);
(c) for every u, Δ Σ_{k not optimal for any queue} E[T_uk(t+1)] ≥ (K − U) D(μ) B(t). -/
theorem corollary_20 {U K : ℕ} (hU : 0 < U) (hUK : U ≤ K) (hK : 2 ≤ K)
    (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hmu : ∀ u k, 0 ≤ mu u k ∧ mu u k ≤ 1) (hA1 : Assumption1 mu kstar)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (π : Policy U K) (hπ : IsAlphaConsistent π α) :
    ∃ τ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, τ < t →
      ((U : ℝ) * ((K : ℝ) - 1) * D mu kstar *
          ((1 - α) * Real.log t - Real.log (4 * K * C)) ≤
        2 * gapMin mu kstar * ∑ u, ∑ k ∈ univ.erase (kstar u), expCount π mu u k t) ∧
      (∀ u : Fin U, ((U : ℝ) - 1) * D mu kstar *
          ((1 - α) * Real.log t - Real.log (4 * K * C)) ≤
        2 * gapMin mu kstar * ∑ k ∈ univ.erase (kstar u), expCount π mu u k t) ∧
      (∀ u : Fin U, ((K : ℝ) - U) * D mu kstar *
          ((1 - α) * Real.log t - Real.log (4 * K * C)) ≤
        gapMin mu kstar *
          ∑ k ∈ univ.filter (fun k => ∀ u', kstar u' ≠ k), expCount π mu u k t) := by sorry

end QueueBandit.LateLower
