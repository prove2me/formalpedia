-- Prove2me | Theorems.Thm_SmartExpediteAudit_lazy_chain_tendsto_stationary
-- name    : SmartExpediteAudit.lazy_chain_tendsto_stationary
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-09T09:06:57.247959+00:00
-- url     : https://prove2.me/theorems/3942dde2-f77a-4d99-9cb3-4cd122d92de1
-- title:
--   Lazy countable Markov chain with an invariant distribution converges to it from its support
-- statement:
--   Let $P$ be a stochastic matrix on a countable set $V$ and let $\pi$ be a probability distribution on $V$ that is invariant, $\sum_y \pi(y)P(y,z)=\pi(z)$ for all $z$. Assume the chain is lazy, $P(z,z)\ge \tfrac12$ for all $z$, and that some state $o$ reaches every state $n$ with $\pi(n)>0$ through steps $a\to b$ with $\pi(a)>0$ and $P(a,b)>0$. Then for every $x$ with $\pi(x)>0$ and every $n$,
--
--   $$\lim_{r\to\infty} P^r(x,n)=\pi(n).$$
--
--   Role: this is the discrete-time convergence to equilibrium that the parent applies to the uniformized Policy-M kernel, before mixing over the Poisson clock to obtain the continuous-time limit $\lim_{t\to\infty}P_t(x,n)=\pi_M(n)$.
--
--   **Formalization Note**: aperiodicity is supplied by laziness and irreducibility by connectivity of the support of $\pi$ from one state $o$; the initial state is required to lie in the support.
-- source:
--   J. R. Norris, Markov Chains, Cambridge University Press 1997, https://doi.org/10.1017/CBO9780511810633, Section 1.8, Theorem 1.8.3 (convergence to equilibrium)

import Mathlib
import Definitions.Def_mm_countable

namespace SmartExpediteAudit

theorem lazy_chain_tendsto_stationary {V : Type*} [Countable V] [DecidableEq V]
    (P : V → V → ℝ) (π : V → ℝ) (hP : MarkovMixing.IsStochasticC P)
    (hπ0 : ∀ y, 0 ≤ π y) (hπ1 : HasSum π 1)
    (hstat : ∀ z, ∑' y, π y * P y z = π z)
    (hlazy : ∀ z, 1 / 2 ≤ P z z) (o : V)
    (hpath : ∀ n, 0 < π n →
      Relation.ReflTransGen (fun a b => 0 < π a ∧ 0 < P a b) o n)
    (x : V) (hx : 0 < π x) (n : V) :
    Filter.Tendsto (fun r => MarkovMixing.stepPow P r x n) Filter.atTop (nhds (π n)) := by sorry

end SmartExpediteAudit
