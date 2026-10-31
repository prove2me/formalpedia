-- Prove2me | Theorems.Thm_TimeDepFolk_Asymptotic_one_shot_deviation
-- name    : TimeDepFolk.Asymptotic.one_shot_deviation
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:19:19.899493+00:00
-- url     : https://prove2.me/theorems/a866d9d8-dce2-4d1b-8972-d4afd5deb39e
-- title:
--   §5.1 Part C and footnote 12, p. 20 — one-shot deviation principle under general discounting
-- statement:
--   Let $\theta$ be an evaluation and $\sigma$ a behavior strategy profile of the repeated game $\Gamma_\theta$. Then $\sigma$ is a subgame perfect equilibrium if and only if no player has a profitable one-shot deviation in any subgame: for every $T\ge1$, every history $h_T\in\mathcal H_T$, every player $i$ and every action $a^i\in A^i$,
--   $$\gamma^i_{\theta[T]}\big((a^i,\sigma^i)|_{h_T},\sigma^{-i}|_{h_T}\big)\le\gamma^i_{\theta[T]}\big(\sigma|_{h_T}\big),$$
--   where $(a^i,\sigma^i)$ plays $a^i$ at the first stage of the subgame and follows $\sigma^i$ afterwards.
--
--   The paper uses this principle to reduce the optimality check of its equilibrium to one-shot deviations, noting that it holds under general discounting because of continuity at infinity: for every evaluation and every $\varepsilon>0$ there is $T$ with $\sum_{t>T}\theta_t<\varepsilon$.
--
--   **Formalization Note.** The subgame after $n$ played stages (the paper's $T=n+1$) has weights `cont θ.θ n`, and `oneShot (restrict σ h) i a` is the profile $(a^i,\sigma^i)|_{h},\sigma^{-i}|_h$. `IsSPE` quantifies over all behavior strategy deviations, so the equivalence is a genuine statement. Deviating to a pure action suffices because a player's payoff is linear in their own first-stage mixed action.
-- source:
--   X. Li, The folk theorem for repeated games with time-dependent discounting, SSRN Working Paper 3407197 (version of August 16, 2019), p. 20, §5.1 Part C and footnote 12

import Mathlib
import Definitions.Def_TimeDepFolk_Asymptotic_Model

namespace TimeDepFolk.Asymptotic

theorem one_shot_deviation {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    {A : I → Type*} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    (g : I → (∀ i, A i) → ℝ) (θ : Evaluation) (σ : Profile A) :
    IsSPE g θ σ ↔ ∀ (n : ℕ) (h : History A n) (i : I) (a : A i),
      payoff g (cont θ.θ n) (oneShot (restrict σ h) i a) i ≤
        payoff g (cont θ.θ n) (restrict σ h) i := by sorry

end TimeDepFolk.Asymptotic
