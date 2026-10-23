-- Prove2me | Theorems.Thm_TimeDepFolk_Asymptotic_theorem_3_1
-- name    : TimeDepFolk.Asymptotic.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:19.877646+00:00
-- url     : https://prove2.me/theorems/8bacdd89-efa4-415b-b090-dfe8deefb6a3
-- title:
--   Theorem 3.1, p. 12 — Asymptotic Perfect Folk Theorem: for patient evaluations θ^k, E_{θ^k} → F in Hausdorff distance when int F ≠ ∅
-- statement:
--   **Asymptotic Perfect Folk Theorem.** Consider a repeated game $\Gamma$ with perfect observation, a finite nonempty player set $I$, finite nonempty action sets $A^i$ and stage payoffs $g:A\to\mathbb R^I$. Let $v^i$ be player $i$'s minmax level against independent mixed actions of the others, $S=\operatorname{co}\{g(a):a\in A\}$, and $\mathcal F=\{x\in S:x^i\ge v^i\ \forall i\}$. For an evaluation $\theta$, let $E_\theta$ be the set of subgame perfect equilibrium payoff vectors of the repeated game $\Gamma_\theta$ with payoff $\gamma_\theta(\sigma)=\mathbb E_\sigma[\sum_t\theta_tg(a_t)]$.
--
--   Let $(\theta^k)_{k\ge1}$ be a sequence of patient evaluations ($\theta^k_t/\theta^k_{t+1}\to1$ uniformly in $t$). If $\operatorname{int}\mathcal F$ is nonempty (so $\mathcal F$ is fully dimensional), then
--   $$E_{\theta^k}\xrightarrow[k\to\infty]{}\mathcal F$$
--   in the Hausdorff distance.
--
--   The theorem extends the Fudenberg–Maskin perfect folk theorem from stationary discounting with $\delta\to1$ to arbitrary time-dependent discounting, with patience expressed through the ratios of consecutive weights, and without public randomization.
--
--   **Formalization Note.** "$\operatorname{int}\mathcal F$ nonempty and fully dimensional" is the single condition `(interior (F g)).Nonempty` in $\mathbb R^I$: a subset of $\mathbb R^I$ with nonempty interior is full-dimensional. The convergence is `Metric.hausdorffEDist` $\to0$ in $[0,\infty]$, with the sup norm on $\mathbb R^I$; since the Hausdorff edistance from the empty set to a nonempty set is $\infty$, the statement includes that $E_{\theta^k}$ is nonempty for all large $k$. The conclusion also contains that $E_{\theta^k}$ lies within vanishing distance of $\mathcal F$ (in fact $E_\theta\subseteq\mathcal F$ always holds), which the paper uses without stating. Stages are 0-based in Lean (see the `Model` definition).
-- source:
--   X. Li, The folk theorem for repeated games with time-dependent discounting, SSRN Working Paper 3407197 (version of August 16, 2019), p. 12, Theorem 3.1

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

namespace TimeDepFolk.Asymptotic

theorem theorem_3_1 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    (g : I → (∀ i, A i) → ℝ) (hint : (interior (F g)).Nonempty)
    (θ : ℕ → Evaluation) (hθ : IsPatient θ) :
    Filter.Tendsto (fun k => Metric.hausdorffEDist (eqPayoffs g (θ k)) (F g))
      Filter.atTop (nhds 0) := by sorry

end TimeDepFolk.Asymptotic
