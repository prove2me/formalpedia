-- Prove2me | Theorems.Thm_QueueBandit_EarlyLower_corollary_20
-- name    : QueueBandit.EarlyLower.corollary_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:33:41.052782+00:00
-- url     : https://prove2.me/theorems/27320cc7-5a8d-48c4-a64b-773aa2879e6d
-- title:
--   Corollary 20, p. 39 — summed sub-optimal schedule counts ≥ U(K−1)D(μ), (U−1)D(μ), (K−U)D(μ) times ((1−α) log t − log(4KC))
-- statement:
--   In the setting of Lemma 19 (a switch with $U\le K$ queues and servers, $K\ge2$, entries of $\mu$ in $[0,1]$, a unique optimal matching $k^*$, and an $\alpha$-consistent policy), there are constants $\tau$ and $C>0$ such that for every $t>\tau$, with $L_t=(1-\alpha)\log t-\log(4KC)$:
--
--   1. $$2\Delta\sum_{u}\sum_{k\neq k^*_u}\mathbb E[T_{uk}(t+1)]\ge U(K-1)\,D(\mu)\,L_t;$$
--   2. for every queue $u$, $$2\Delta\sum_{k\neq k^*_u}\mathbb E[T_{uk}(t+1)]\ge (U-1)\,D(\mu)\,L_t;$$
--   3. for every queue $u$, $$\Delta\sum_{k\notin\{k^*_1,\dots,k^*_U\}}\mathbb E[T_{uk}(t+1)]\ge (K-U)\,D(\mu)\,L_t .$$
--
--   Here $D(\mu)=\Delta/\mathrm{KL}(\mu_{\min},(\mu^*+1)/2)$. These bounds on the total number of sub-optimal schedules are what Theorem 8 combines with Lemma 22.
--
--   **Formalization Note.** The paper writes part 3's sum as $\sum_{k>U}$, after relabelling the servers so that the first $U$ are the optimal ones (p. 38). Without the relabelling this is the sum over the servers that are optimal for no queue. One pair $(\tau,C)$ serves all three parts, as printed, and $C>0$ is added without loss of generality. $D(\mu)=0$ when $\mu^*=1$.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 39, Corollary 20; proof pp. 40–41

import Mathlib
import Definitions.Def_QueueBandit_EarlyLower_Model
import Definitions.Def_QueueBandit_LateLower_Dynamics

namespace QueueBandit.EarlyLower

/-- Corollary 20 (arXiv:1604.06377v4, p. 39). For an instance with a unique optimal matching and an
`α`-consistent policy there are `τ` and `C > 0` such that for every `t > τ`, writing
`L = (1 − α) log t − log(4KC)`:
(a) `2Δ Σ_u Σ_{k ≠ k*_u} E[T_{uk}(t+1)] ≥ U(K − 1) D(μ) L`;
(b) for every `u`, `2Δ Σ_{k ≠ k*_u} E[T_{uk}(t+1)] ≥ (U − 1) D(μ) L`;
(c) for every `u`, `Δ Σ_{k} E[T_{uk}(t+1)] ≥ (K − U) D(μ) L`, the sum over the servers `k` that are
optimal for no queue (the paper's `k > U` after relabelling). -/
theorem corollary_20 {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (hU : 0 < U)
    (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hmu : ∀ u k, 0 ≤ mu u k ∧ mu u k ≤ 1) (hA1 : QueueBandit.LateLower.Assumption1 mu kstar)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (π : QueueBandit.LateLower.Policy U K)
    (hπ : QueueBandit.LateLower.IsAlphaConsistent π α) :
    ∃ τ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t : ℕ, τ < t →
      ((U : ℝ) * ((K : ℝ) - 1) * QueueBandit.LateLower.D mu kstar *
            ((1 - α) * Real.log t - Real.log (4 * K * C)) ≤
          2 * QueueBandit.LateLower.gapMin mu kstar *
            ∑ u : Fin U, ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u),
              QueueBandit.LateLower.expCount π mu u k t) ∧
      (∀ u : Fin U,
        ((U : ℝ) - 1) * QueueBandit.LateLower.D mu kstar *
            ((1 - α) * Real.log t - Real.log (4 * K * C)) ≤
          2 * QueueBandit.LateLower.gapMin mu kstar *
            ∑ k ∈ Finset.univ.filter (fun k : Fin K => k ≠ kstar u),
              QueueBandit.LateLower.expCount π mu u k t) ∧
      (∀ u : Fin U,
        ((K : ℝ) - U) * QueueBandit.LateLower.D mu kstar *
            ((1 - α) * Real.log t - Real.log (4 * K * C)) ≤
          QueueBandit.LateLower.gapMin mu kstar *
            ∑ k ∈ Finset.univ.filter (fun k : Fin K => ∀ u' : Fin U, kstar u' ≠ k),
              QueueBandit.LateLower.expCount π mu u k t) := by sorry

end QueueBandit.EarlyLower
