-- Prove2me | Theorems.Thm_RoundRobinEq_CancelableBluff_lemma_3_3
-- name    : RoundRobinEq.CancelableBluff.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:28:13.322704+00:00
-- url     : https://prove2.me/theorems/980b6fe8-7a8e-427e-966c-053bc461f8fd
-- title:
--   Lemma 3.3 — good-by-good singleton domination implies set domination for cancelable valuations
-- statement:
--   Let $v : 2^M \to \mathbb R$ be a cancelable valuation function (normalized and non-decreasing). Let $X = \{x_1, \dots, x_k\}$ and $Y = \{y_1, \dots, y_k\}$ be two sets of $k$ distinct goods each ($X$ and $Y$ may share goods). If
--   $$
--   v(\{x_j\}) \ge v(\{y_j\}) \quad \text{for every } j \in [k],
--   $$
--   then $v(X) \ge v(Y)$.
--
--   For additive valuations the statement is immediate; the lemma extends it to cancelable valuations, which need not be additive. It is used to finish the proof of Theorem 3.2 (agent $i$'s bluff bundle against her deviation bundle) and in the proof of Proposition 2.5.
--
--   **Formalization Note** The goods are given by injective maps `x y : Fin k → M`, so $X$ and $Y$ are their images and have exactly $k$ elements; nothing prevents $x_j = y_t$. The page writes $v(x_j)$ for the singleton value $v(\{x_j\})$, which is `v {x j}`.
-- source:
--   Amanatidis et al., Round-Robin Beyond Additive Agents, arXiv:2301.13652v1, p. 8, Lemma 3.3

import Mathlib
import Definitions.Def_RoundRobinEq_CancelableBluff_Setting

namespace RoundRobinEq.CancelableBluff

theorem lemma_3_3 {M : Type*} [DecidableEq M] (v : Finset M → ℝ) (hv : IsValuation v)
    (hc : IsCancelable v) {k : ℕ} (x y : Fin k → M) (hx : Function.Injective x)
    (hy : Function.Injective y) (hxy : ∀ j : Fin k, v {y j} ≤ v {x j}) :
    v (Finset.univ.image y) ≤ v (Finset.univ.image x) := by sorry

end RoundRobinEq.CancelableBluff
