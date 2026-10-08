-- Prove2me | Theorems.Thm_RetailVariety_Structure_h_endpoints
-- name    : RetailVariety.Structure.h_endpoints
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:41:03.259253+00:00
-- url     : https://prove2.me/theorems/b5dd3b53-65c0-44a5-9c32-affef992ef72
-- title:
--   §3.1: $h(v_j)=\pi(S\cup\{j\},v)$ for $j\notin S$, and $h(0)=\pi(S,v)$
-- statement:
--   Let $v_j>0$, $v_0>0$, $0<c<p$, $\lambda>0$, $\sigma>0$, $0\le\beta<1$, and let $S\subseteq N$ be an assortment. With $h_I$, $h_T$ as in Lemma 1:
--
--   1. for every variant $j\notin S$, $h_I(v_j)=\pi_I(S\cup\{j\},v)$;
--   2. for every variant $j\notin S$, $h_T(v_j)=\pi_T(S\cup\{j\},v)$;
--   3. $h_T(0)=\pi_T(S,v)$;
--   4. if $\beta>0$, then $h_I(0)=\pi_I(S,v)$.
--
--   In words, $h(\delta)$ is the profit of adding a variant of preference $\delta$ to $S$: at $\delta=0$ nothing is added and at $\delta=v_j$ variant $j$ is added.
--
--   **Formalization Note** Clause 4 needs $\beta>0$: $g_I$ contains $\delta^\beta$, and at $\beta=0$ the convention $0^0=1$ (which also makes $\sum_{j\in S}q_j^0$ count the variants of $S$, as in (7)) gives $g_I(0)$ one extra unit of the safety-stock term, so $h_I(0)<\pi_I(S,v)$ there. Clause 2 relies on $\lambda$ multiplying both terms of $g_T$; with (11) as printed it fails unless $\lambda=1$.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1503, §3.1, paragraph after Lemma 1

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model

namespace RetailVariety.Structure

/-- §3.1, p. 1503 (after Lemma 1): `h_I(v_j) = π_I(S ∪ {j}, v)` and `h_T(v_j) = π_T(S ∪ {j}, v)`
for `j ∉ S`; `h_T(0) = π_T(S, v)`; and, when `0 < β`, `h_I(0) = π_I(S, v)`. (At `β = 0`,
Lean's `0 ^ 0 = 1` puts an extra unit into `g_I(0)`.) -/
theorem h_endpoints {n : ℕ} (v : Fin n → ℝ) (v0 : ℝ) (hv : ∀ j, 0 < v j) (hv0 : 0 < v0)
    (p c lam σ β : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam) (hσ : 0 < σ)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (S : Finset (Fin n)) :
    (∀ j, j ∉ S → hI p c lam σ β v v0 S (v j) = profitI p c lam σ β v v0 (insert j S)) ∧
      (∀ j, j ∉ S → hT p c lam v v0 S (v j) = profitT p c lam v v0 (insert j S)) ∧
      hT p c lam v v0 S 0 = profitT p c lam v v0 S ∧
      (0 < β → hI p c lam σ β v v0 S 0 = profitI p c lam σ β v v0 S) := by sorry

end RetailVariety.Structure
