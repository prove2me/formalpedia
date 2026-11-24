-- Prove2me | Theorems.Thm_SteinitzExchange_Duality_Supplement_truncation_valuation
-- name    : SteinitzExchange.Duality.Supplement.truncation_valuation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T04:33:09.55446+00:00
-- url     : https://prove2.me/theorems/af6fbcc5-e901-480b-8d1c-3e99b1cfc07b
-- title:
--   Theorem 7.5 — the truncation of a valuated matroid is a valuated matroid
-- statement:
--   Let $\mathbf M=(E,\mathcal B)$ be a matroid on a finite set $E$ with valuation $\omega:\mathcal B\to\mathbb R$, and let $k$ be an integer with $0\le k\le\operatorname{rank}\mathbf M$. Let
--   $$\mathcal B_k=\{X\subseteq E\mid |X|=k,\ \exists B:\ X\subseteq B\in\mathcal B\},\qquad \omega_k(X)=\max\{\omega(B)\mid X\subseteq B\in\mathcal B\}\quad(X\in\mathcal B_k).$$
--   Then $\omega_k$ is a valuation of the truncation $\mathbf M_k=(E,\mathcal B_k)$; that is, $\mathcal B_k$ is a matroid base family and $\omega_k$ satisfies (MV) on it.
--
--   The result is due to Murota [31]; the paper gives an alternative proof through bipartite induction.
--
--   **Formalization Note.** $\operatorname{rank}\mathbf M$ is `matroidRank ℬ`, the largest cardinality of a base (all bases of a matroid have the same size). $k$ is a natural number, so $k=0$ is included, with $\mathcal B_0=\{\emptyset\}$.
--
--   Differences from the source: none.
-- source:
--   Murota, Convexity and Steinitz's Exchange Property, Adv. Math. 124 (1996), p. 307, Theorem 7.5 (with the definitions of M_k and ω_k on p. 306)

import Mathlib
import Definitions.Def_SteinitzExchange_Duality_Supplement_ValuatedMatroid
import Definitions.Def_SteinitzExchange_Duality_Supplement_MatroidTruncation

namespace SteinitzExchange.Duality.Supplement

/-- Murota 1996, p. 307, Theorem 7.5. Let `M = (E, ℬ)` be a matroid with valuation `ω` and
`k ≤ rank M`. Then `ω_k(X) = max{ω(B) | X ⊆ B ∈ ℬ}` is a valuation of the truncation
`M_k = (E, ℬ_k)`, `ℬ_k = {X ⊆ E | |X| = k, ∃ B : X ⊆ B ∈ ℬ}`. -/
theorem truncation_valuation {E : Type*} [Fintype E] [DecidableEq E]
    (ℬ : Finset (Finset E)) (ω : Finset E → ℝ) (h : IsValuatedMatroid ℬ ω) (k : ℕ)
    (hk : k ≤ matroidRank ℬ) :
    IsValuatedMatroid (truncBases ℬ k) (truncValue ℬ ω) := by sorry

end SteinitzExchange.Duality.Supplement
