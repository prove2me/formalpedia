-- Prove2me | Theorems.Thm_OrdinalMSP_Forbidden_optimal_p
-- name    : OrdinalMSP.Forbidden.optimal_p
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:38.39678+00:00
-- url     : https://prove2.me/theorems/151c2704-e6b7-47c0-8f54-7840deba31ec
-- title:
--   Proof of Lemma 1, p. 10 — optimizing p: the bound is maximized at p = p(k), with value 1/α(k)
-- statement:
--   Let $k \ge 1$ be an integer and let
--   $$g_k(p) = \begin{cases} -p\ln p, & k = 1,\\[4pt] \dfrac{p - p^k}{k-1}, & k \ge 2,\end{cases}$$
--   be the lower bound on $\Pr(r^* \in \mathrm{ALG})$ obtained for sampling probability $p$. With $(p(k), \alpha(k)) = (1/e, e)$ for $k = 1$ and $(k^{-1/(k-1)}, k^{k/(k-1)})$ for $k \ge 2$:
--   1. $p(k) \in (0, 1]$ is an admissible sampling probability;
--   2. $g_k(p(k)) = 1/\alpha(k)$;
--   3. $p(k)$ maximizes $g_k$ over $(0,1]$: $g_k(p) \le g_k(p(k))$ for every $p \in (0, 1]$.
--
--   This is the last step of the proof of the Key Lemma: "by optimizing the value of $p$ as a function of $k$", the guaranteed selection probability is $1/\alpha(k)$, attained at $p = p(k)$.
--
--   **Formalization Note** $g_k$ is passed as a function `g` together with its defining equation, which branches on $k = 1$ first. $p(k)$ and $\alpha(k)$ are `pK k` and `alphaK k` of the Setting definition (`Real.exp`, `Real.rpow`). The page writes "the probability of $r^* \in \mathrm{ALG}$ is $1/\alpha(k)$"; the formal content is that the lower bound $g_k$ attains the value $1/\alpha(k)$ at $p(k)$ and that no other $p$ does better.
-- source:
--   Soto, Turkieltaub & Verdugo, Strong Algorithms for the Ordinal Matroid Secretary Problem, arXiv:1802.01997v1, proof of Lemma 1, p. 10, last sentence ("By optimizing the value of p as a function of k, …")

import Mathlib
import Definitions.Def_OrdinalMSP_Forbidden_Setting

namespace OrdinalMSP.Forbidden

theorem optimal_p (k : ℕ) (hk : 1 ≤ k) (g : ℝ → ℝ)
    (hg : ∀ p, g p = if k = 1 then -p * Real.log p else (p - p ^ k) / ((k : ℝ) - 1)) :
    pK k ∈ Set.Ioc 0 1 ∧ g (pK k) = 1 / alphaK k ∧ ∀ p ∈ Set.Ioc (0 : ℝ) 1, g p ≤ g (pK k) := by sorry

end OrdinalMSP.Forbidden
