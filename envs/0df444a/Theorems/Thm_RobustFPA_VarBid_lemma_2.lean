-- Prove2me | Theorems.Thm_RobustFPA_VarBid_lemma_2
-- name    : RobustFPA.VarBid.lemma_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:19:39.275478+00:00
-- url     : https://prove2.me/theorems/39003219-de7c-420f-8dd6-1b6fed7dc39b
-- title:
--   Lemma 2 (proof of Proposition 4) — $\max\{\tilde b, L\}$ maximizes $u^+$ on $[L,\infty)$
-- statement:
--   Let $n \ge 2$, $0 < \tau < 1$ and $L < v$. With $p(b) = (b-L)/(v-L)$, $u^+(b) = (v-b)(1-\tau+\tau p(b))^{n-1}$ and $\tilde b = v - (v-L)/(n\tau)$,
--   $$
--   \max\{\tilde b, L\} \in \arg\sup_{\hat b \ge L} u^+(\hat b),
--   $$
--   that is, $\max\{\tilde b, L\} \ge L$ and $u^+(\hat b) \le u^+(\max\{\tilde b, L\})$ for every $\hat b \ge L$.
--
--   The lemma identifies the best response to the worst case for bidding too high, in which all unconstrained opponents bid $L$; it is the first step in reducing the set $X$ of Proposition 3 to the solutions of Equation (3).
--
--   **Formalization Note.** $u^+$ is the polynomial of the ClosedForms file on all of $\mathbb R$; for $\hat b > v$ it is negative, so the supremum over $[L, \infty)$ is the paper's.
-- source:
--   Kasberger & Schlag, Robust Bidding in First-Price Auctions, SSRN 3044438 (version of 3 Sep 2022), p. 49, Lemma 2 (Appendix B.4, proof of Proposition 4)

import Mathlib
import Definitions.Def_RobustFPA_VarBid_ClosedForms

namespace RobustFPA.VarBid

theorem lemma_2 (n : ℕ) (hn : 2 ≤ n) (τ L v : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (hLv : L < v) :
    L ≤ max (bTilde n τ L v) L ∧
    ∀ b : ℝ, L ≤ b → uPlus n τ L v b ≤ uPlus n τ L v (max (bTilde n τ L v) L) := by sorry

end RobustFPA.VarBid
