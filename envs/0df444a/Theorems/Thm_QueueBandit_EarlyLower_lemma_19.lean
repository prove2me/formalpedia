-- Prove2me | Theorems.Thm_QueueBandit_EarlyLower_lemma_19
-- name    : QueueBandit.EarlyLower.lemma_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T23:33:32.044831+00:00
-- url     : https://prove2.me/theorems/c525abd8-e467-4b4d-b133-9c24ccb344a6
-- title:
--   Lemma 19, p. 37 — α-consistency forces E[T_uk(t+1)] + Σ_{u′≠u} 1{k*_{u′}=k} E[T_{u′k*_u}(t+1)] ≥ ((1−α) log t − log(4KC))/KL(μ_min, (μ*+1)/2)
-- statement:
--   Consider the $U\times K$ switch with service probabilities $\mu$ (entries in $[0,1]$), a unique optimal matching $k^*$, $U\le K$, $K\ge2$, and fix $\alpha\in(0,1)$ and an $\alpha$-consistent scheduling policy. Write $T_{uk}(t+1)=\sum_{s=1}^t\mathbb 1\{\kappa_u(s)=k\}$. Then there are constants $\tau$ and $C>0$ such that for every queue $u$, every server $k\neq k^*_u$ and every $t>\tau$,
--
--   $$\mathbb E[T_{uk}(t+1)]+\sum_{u'\neq u}\mathbb 1\{k^*_{u'}=k\}\,\mathbb E[T_{u'k^*_u}(t+1)]\;\ge\;\frac{1}{\mathrm{KL}\big(\mu_{\min},\frac{\mu^*+1}{2}\big)}\Big((1-\alpha)\log t-\log(4KC)\Big).$$
--
--   It is a non-asymptotic, Lai–Robbins-type lower bound on how often an $\alpha$-consistent policy must schedule sub-optimal links. It is the input to Corollary 20.
--
--   **Formalization Note.** The constants $\tau,C$ are chosen after the instance and the policy, as printed. $C>0$ is added so that $\log(4KC)$ is meaningful; this is without loss of generality. The arrival rates play no role, since the schedule does not depend on them, so the statement quantifies over $\mu$ only. $1/\mathrm{KL}$ is read as $0$ when $\mu^*=1$. $K\ge2$ and $U\ge1$ are standing assumptions of the mission.
-- source:
--   Krishnasamy, Sen, Johari and Shakkottai, arXiv:1604.06377v4, p. 37, Lemma 19; proof pp. 38–39

import Mathlib
import Definitions.Def_QueueBandit_EarlyLower_Model
import Definitions.Def_QueueBandit_LateLower_Dynamics

namespace QueueBandit.EarlyLower

/-- Lemma 19 (arXiv:1604.06377v4, p. 37). For an instance with a unique optimal matching and an
`α`-consistent policy there are `τ` and `C > 0` such that for every queue `u`, every `k ≠ k*_u`
and every `t > τ`,
`E[T_{uk}(t+1)] + Σ_{u' ≠ u} 1{k*_{u'} = k} E[T_{u' k*_u}(t+1)]
  ≥ (1 / KL(μ_min, (μ*+1)/2)) ((1 − α) log t − log(4KC))`. -/
theorem lemma_19 {U K : ℕ} (hUK : U ≤ K) (hK : 2 ≤ K) (hU : 0 < U)
    (mu : Fin U → Fin K → ℝ) (kstar : Fin U → Fin K)
    (hmu : ∀ u k, 0 ≤ mu u k ∧ mu u k ≤ 1) (hA1 : QueueBandit.LateLower.Assumption1 mu kstar)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (π : QueueBandit.LateLower.Policy U K)
    (hπ : QueueBandit.LateLower.IsAlphaConsistent π α) :
    ∃ τ : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ u : Fin U, ∀ k : Fin K, k ≠ kstar u → ∀ t : ℕ, τ < t →
      QueueBandit.LateLower.invKL mu * ((1 - α) * Real.log t - Real.log (4 * K * C)) ≤
        QueueBandit.LateLower.expCount π mu u k t +
          ∑ u' ∈ Finset.univ.filter (fun u' : Fin U => u' ≠ u),
            (if kstar u' = k then QueueBandit.LateLower.expCount π mu u' (kstar u) t else 0) := by sorry

end QueueBandit.EarlyLower
