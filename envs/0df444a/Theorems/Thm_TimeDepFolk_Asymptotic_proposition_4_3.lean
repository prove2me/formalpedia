-- Prove2me | Theorems.Thm_TimeDepFolk_Asymptotic_proposition_4_3
-- name    : TimeDepFolk.Asymptotic.proposition_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:28.760533+00:00
-- url     : https://prove2.me/theorems/602681bc-8ad3-4be5-9fe0-9bb92c5d98c0
-- title:
--   Proposition 4.3, p. 16 — every x ∈ F is the θ^k-payoff of a pure path whose continuation payoffs stay η-close to x, K(η) uniform in x
-- statement:
--   Consider a repeated game with finite player set $I$, finite action sets $A^i$ and stage payoffs $g$, and let $\mathcal F$ be its set of feasible and individually rational payoff vectors. Let $(\theta^k)_{k\ge1}$ be a sequence of patient evaluations. For every $\eta>0$ there is $K(\eta)$, independent of $x$, such that for every $x\in\mathcal F$ and every $k\ge K(\eta)$ there is a sequence of pure action profiles $h_\infty=(a_t)_{t\ge1}$ with
--
--   1. $\gamma_{\theta^k}(h_\infty)=\sum_{t\ge1}\theta^k_t\,g(a_t)=x$;
--   2. after any stage $T\ge1$, $\big\|\gamma_{\theta^k[T+1]}(h^T_\infty)-x\big\|_\infty\le\eta$, where $h_\infty=(a_1,\dots,a_T,h^T_\infty)$.
--
--   The proposition removes public randomization: a target payoff is reached exactly by a deterministic path, and at every point along the path the remaining payoff is still close to the target.
--
--   **Formalization Note.** After $T$ played stages the continuation weights are `cont (θ k).θ T` (the paper's $\theta^k[T+1]$) and the continuation path is `fun s => h (T + s)`. The order of quantifiers $\forall\eta\,\exists K\,\forall x\in\mathcal F\,\forall k\ge K$ is the page's "such integer $K(\eta)$ can be chosen independent of $x$". The statement is for all $x\in\mathcal F$, as printed.
-- source:
--   X. Li, The folk theorem for repeated games with time-dependent discounting, SSRN Working Paper 3407197 (version of August 16, 2019), p. 16, Proposition 4.3 (proof §7.2, pp. 36–37)

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

namespace TimeDepFolk.Asymptotic

theorem proposition_4_3 {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    (g : I → (∀ i, A i) → ℝ) (θ : ℕ → Evaluation) (hθ : IsPatient θ) :
    ∀ η > 0, ∃ K : ℕ, ∀ x ∈ F g, ∀ k ≥ K, ∃ h : ℕ → (∀ i, A i),
      purePayoff g (θ k).θ h = x ∧
        ∀ T ≥ 1, ‖purePayoff g (cont (θ k).θ T) (fun s => h (T + s)) - x‖ ≤ η := by sorry

end TimeDepFolk.Asymptotic
