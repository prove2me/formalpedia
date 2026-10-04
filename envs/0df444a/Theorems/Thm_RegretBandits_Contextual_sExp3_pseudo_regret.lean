-- Prove2me | Theorems.Thm_RegretBandits_Contextual_sExp3_pseudo_regret
-- name    : RegretBandits.Contextual.sExp3_pseudo_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T10:49:43.509816+00:00
-- url     : https://prove2.me/theorems/30e61a28-aa22-4557-90df-fcd4968826be
-- title:
--   Theorem 4.1 — pseudo-regret of S-Exp3 with side information
-- statement:
--   Let $K \ge 2$ arms, let $\mathcal S$ be a finite set of contexts and let $s_1, s_2, \dots \in \mathcal S$ be a fixed context sequence. Let the losses $\ell_{i,t} \in [0,1]$ be assigned by an adversary that may adapt to the forecaster's past plays. Run the S-Exp3 forecaster, which runs one Exp3 instance per context with learning rate $\eta_s = \sqrt{2\ln K/(n_s K)}$, where $n_s$ is the number of the first $n$ rounds marked by $s$. Then for every map $g : \mathcal S \to \{1,\dots,K\}$,
--   $$\mathbb E\left[\sum_{t=1}^n \ell_{I_t,t} - \sum_{t=1}^n \ell_{g(s_t),t}\right] \le \sqrt{2 n |\mathcal S| K \ln K},$$
--   that is, the side-information pseudo-regret $\overline R^{\mathcal S}_n = \max_g \mathbb E[\cdots]$ is at most $\sqrt{2n|\mathcal S|K\ln K}$.
--
--   The forecaster competes with the best mapping from contexts to arms at the price of a factor $\sqrt{|\mathcal S|}$ over the context-free bound (3.2).
--
--   **Formalization Note** The book states "there exists a randomized forecaster"; the Lean statement names the forecaster of the book's proof (S-Exp3 with the tuning of (3.2) on each context), which depends on $n$ and the context sequence but not on the losses. The maximum over $g$ is written as "for every $g$". The adversary is a deterministic function of past plays.
-- source:
--   Bubeck, Cesa-Bianchi, Regret Analysis of Stochastic and Nonstochastic Multi-armed Bandit Problems, arXiv:1204.5721v2, p. 44, Theorem 4.1

import Mathlib
import Definitions.Def_RegretBandits_Contextual_Protocol
import Definitions.Def_RegretBandits_Contextual_SExp3

namespace RegretBandits.Contextual

/-- Theorem 4.1 (Bubeck–Cesa-Bianchi, arXiv:1204.5721v2, p. 44): the S-Exp3 forecaster, run with
the per-context rates `η_c = √(2 ln K / (n_c K))` on a fixed context sequence `s` from a finite set
`S`, against any adaptive adversary with losses in `[0,1]`, satisfies, for every map
`g : S → {1, …, K}`,
`E[∑_{t ≤ n} ℓ_{I_t,t} - ∑_{t ≤ n} ℓ_{g(s_t),t}] ≤ √(2 n |S| K ln K)`. -/
theorem sExp3_pseudo_regret {S : Type*} [Fintype S] [DecidableEq S] {K : ℕ} (hK : 2 ≤ K)
    (n : ℕ) (s : ℕ → S) (ℓ : AdaptiveLosses K)
    (hℓ : ∀ t h i, 0 ≤ ℓ t h i ∧ ℓ t h i ≤ 1) (g : S → Fin K) :
    pathExpect (sExp3Rule (sExp3Rate K n s) s ℓ) n
        (fun ω => ∑ t : Fin n,
          (ℓ t (playPrefix ω t) (ω t) - ℓ t (playPrefix ω t) (g (s t)))) ≤
      Real.sqrt (2 * n * Fintype.card S * K * Real.log K) := by sorry

end RegretBandits.Contextual
