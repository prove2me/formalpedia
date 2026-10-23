-- Prove2me | Theorems.Thm_TailOptCaching_ETLRU_theorem_2
-- name    : TailOptCaching.ETLRU.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:33.304363+00:00
-- url     : https://prove2.me/theorems/1be6207c-7803-4b63-93d6-6f3127245d35
-- title:
--   Theorem 2, p. 9 — Expected-Tail-Optimized LRU is an optimal online caching policy for Tail Excess Latency in the stochastic conversation model
-- statement:
--   **Theorem 2 (Optimality of Expected-Tail-Optimized LRU).** In the stochastic conversation model — conversations born at rate $\lambda_{\mathrm{conv}} > 0$, returning at rates $\bar\lambda_i > 0$ while active, with exponentially distributed lifetimes tracked through belief rates, known prompt-length laws, arbitrary response-length laws, cache capacity $C$ and threshold $\xi \ge 0$ — let $\sigma$ be any ET-LRU policy (Definition 1) and let $\pi$ be any caching policy whose decisions always satisfy (9), (10) and the capacity constraint. Then for every number $M$ of requests and every well-formed starting belief state $z$,
--   $$\mathbb E^\sigma\Big[\sum_{k=1}^{M} \mathrm{TEL}_k\Big] \le \mathbb E^\pi\Big[\sum_{k=1}^{M} \mathrm{TEL}_k\Big],$$
--   where $\mathrm{TEL}_k = (L_\theta + Q - X_\theta - \xi)^+$ is the Tail Excess Latency of the $k$-th request.
--
--   ET-LRU is myopic: it minimizes only the expected TEL of the next turn. The theorem says that, in this model, myopia loses nothing over any horizon. With $\xi = 0$ and homogeneous rates it specializes to the optimality of LRU for average latency.
--
--   **Formalization Note.** Policies are Markov and deterministic: they map the stage, the belief state and the current arrival to a cache vector. The well-formedness hypothesis ($0 < \lambda_i \le \bar\lambda_i$ for arrived conversations, $X_i \le L_i$, $\sum_i X_i \le C$, nothing beyond the arrived conversations) holds for the empty start and for every reachable state; it cannot be dropped, since the claim fails from some states with $\lambda_i > \bar\lambda_i$. The law of the decay factor $e^{-\mu\tau}$ is generalized to any probability law on $(0,1]$ depending on the belief rates, which contains the paper's law. Values are in $[0,\infty]$.
-- source:
--   Zhang, Li, Moallemi & Peng, Tail-Optimized Caching for LLM Inference, arXiv:2510.15152v1, p. 9, Theorem 2

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Model

open scoped ENNReal

namespace TailOptCaching.ETLRU

theorem theorem_2 (P : Params) (σ : Policy) (hσ : IsETLRU P σ)
    (π : Policy) (hπ : Admissible P π) (M : ℕ) (z : State) (hz : WellFormed P z) :
    value P σ M 0 z ≤ value P π M 0 z := by sorry

end TailOptCaching.ETLRU
