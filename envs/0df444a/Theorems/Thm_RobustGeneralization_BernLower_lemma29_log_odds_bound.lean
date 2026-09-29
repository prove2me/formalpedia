-- Prove2me | Theorems.Thm_RobustGeneralization_BernLower_lemma29_log_odds_bound
-- name    : RobustGeneralization.BernLower.lemma29_log_odds_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:20:13.523233+00:00
-- url     : https://prove2.me/theorems/6292603d-359c-4224-8db7-77f3f8f29981
-- title:
--   Lemma 29 — with prob. 1 − δ, |log posterior odds| ≤ 15τ√(2n log(2/δ))
-- statement:
--   Let $\theta$ be uniform on $\{-1,+1\}$ and let $(x_1,y_1),\dots,(x_n,y_n)$ be drawn independently from the one-dimensional $(\theta,\tau)$-Bernoulli model ($y_k$ uniform, $x_k=y_k\theta$ with probability $\tfrac12+\tau$, else $x_k=-y_k\theta$). Suppose $0<\tau\le\tfrac14$, $n\le 1/\tau^2$ and $\delta>0$. Then, with probability at least $1-\delta$ over the joint draw of $\theta$ and the samples $S$,
--   $$\log\frac{\Pr[\theta=+1\mid S]}{\Pr[\theta=-1\mid S]}\in\left[-15\tau\sqrt{2n\log\tfrac2\delta},\ 15\tau\sqrt{2n\log\tfrac2\delta}\right].$$
--
--   The lemma quantifies how little $n\le1/\tau^2$ samples reveal about a single sign $\theta$: the posterior stays close to uniform. Applied to each coordinate of $\theta^\star$ it controls the posterior means in the proof of Theorem 31.
--
--   **Formalization Note** The probability is a finite sum of the joint weights $\tfrac12\prod_k P_{\theta,\tau}(x_k,y_k)$ over $\theta$ and $S$. The hypothesis $\delta>0$ is added: at $\delta=0$ Lean's conventions $2/0=0$ and $\log 0=0$ would collapse the interval to $\{0\}$ and make the statement false. For $\delta\ge1$ the statement is trivially true, so no upper bound on $\delta$ is imposed.
-- source:
--   Schmidt, Santurkar, Tsipras, Talwar, Mądry, Adversarially Robust Generalization Requires More Data, arXiv:1804.11285v2, p. 33, Lemma 29

import Mathlib
import Definitions.Def_RobustGeneralization_BernLower_Model

namespace RobustGeneralization.BernLower

theorem lemma29_log_odds_bound (n : ℕ) (τ δ : ℝ) (hτ : 0 < τ) (hτ' : τ ≤ 1 / 4)
    (hn : (n : ℝ) ≤ 1 / τ ^ 2) (hδ : 0 < δ) :
    1 - δ ≤ ∑ θ : Bool, (1 / 2) * ∑ S : Fin n → Bool × Bool,
      (∏ k, bern1W θ τ (S k)) *
        (if |Real.log (odds1 τ S)| ≤ 15 * τ * Real.sqrt (2 * n * Real.log (2 / δ))
          then 1 else 0) := by sorry

end RobustGeneralization.BernLower
