-- Prove2me | Theorems.Thm_TailOptCaching_ETLRU_next_turn_expected_TEL
-- name    : TailOptCaching.ETLRU.next_turn_expected_TEL
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:23:29.306833+00:00
-- url     : https://prove2.me/theorems/5c74292c-85ba-46d8-9591-e888bdce3fcc
-- title:
--   §5, pp. 8–9 — the expected TEL of the next turn equals the objective of (8), up to the normalization and the new-conversation term
-- statement:
--   Let $z = (\lambda, L, X)$ be a well-formed post-decision state with $n$ arrived conversations, and let $d \in (0, 1]$ be the decay factor until the next arrival. With the decayed rates $d\lambda_i$, the next arrival is conversation $i < n$ with probability $d\lambda_i / S$ and a new conversation with probability $\lambda_{\mathrm{conv}}/S$, where $S = \lambda_{\mathrm{conv}} + d\sum_i \lambda_i$. Then the expected TEL of the next arrival satisfies
--   $$S \cdot \mathbb E\big[(L_\theta + Q_\theta - X_\theta - \xi)^+\big] = d \sum_{i < n} \lambda_i\, \mathbb E\big[(L_i + Q_i - X_i - \xi)^+\big] + \lambda_{\mathrm{conv}}\, \mathbb E\big[(Q_{n} - \xi)^+\big],$$
--   where $Q_n$ is the prompt length of the new conversation.
--
--   This is the paper's observation that "$\lambda_i(t^+)\,\mathbb E[(L_i(t^+) + Q_i - X'_i - \xi)^+]$ is the expected TEL contributed by conversation $i$": the next-turn expected TEL is an increasing affine function of the objective of (8), with a term that no caching decision affects.
--
--   **Formalization Note.** The identity is stated multiplied through by $S > 0$, in $[0, \infty]$.
-- source:
--   Zhang, Li, Moallemi & Peng, Tail-Optimized Caching for LLM Inference, arXiv:2510.15152v1, pp. 8–9, §5 (paragraph after Definition 1)

import Mathlib
import Definitions.Def_TailOptCaching_ETLRU_Model

open scoped ENNReal

namespace TailOptCaching.ETLRU

theorem next_turn_expected_TEL (P : Params) (z : State) (hz : WellFormed P z) (d : ℝ)
    (hd : 0 < d) (hd1 : d ≤ 1) :
    arrivalExp P (decay d z) (fun θ q _ => stageCost P (decay d z) θ q) *
        ENNReal.ofReal (P.lamConv + d * ∑ i ∈ Finset.range z.n, z.lam i) =
      ENNReal.ofReal d * nextTEL P z +
        ENNReal.ofReal P.lamConv * ∑' Q : ℕ, P.Qlaw z.n Q * ENNReal.ofReal ((Q : ℝ) - P.ξ) := by sorry

end TailOptCaching.ETLRU
