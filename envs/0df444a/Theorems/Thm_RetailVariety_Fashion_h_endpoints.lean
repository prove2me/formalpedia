-- Prove2me | Theorems.Thm_RetailVariety_Fashion_h_endpoints
-- name    : RetailVariety.Fashion.h_endpoints
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:59:17.05421+00:00
-- url     : https://prove2.me/theorems/867f5947-0d92-4b01-ae5f-bbbdf077ea31
-- title:
--   p. 1503 — $h(0)=\pi(S,v)$ and $h(v_j)=\pi(S\cup\{j\},v)$ for $j\notin S$
-- statement:
--   In the setting of Lemma 1, with $0<\beta<1$, preferences $v_j\ge 0$, any assortment $S$ and any variant $j\notin S$,
--   $$h_I(0)=\pi_I(S,v),\qquad h_I(v_j)=\pi_I(S\cup\{j\},v),$$
--   $$h_T(0)=\pi_T(S,v),\qquad h_T(v_j)=\pi_T(S\cup\{j\},v).$$
--
--   These identities turn quasi-convexity of $h$ into a comparison of profits of actual assortments: the value of $h$ at any point between $0$ and $v_j$ is at most the larger of $\pi(S,v)$ and $\pi(S\cup\{j\},v)$.
--
--   **Formalization Note.** The independent-model identity $h_I(0)=\pi_I(S,v)$ needs $\beta>0$: with real powers $0^0=1$, so at $\beta=0$ the term $\delta^\beta$ does not vanish at $\delta=0$.
-- source:
--   van Ryzin & Mahajan, On the Relationship Between Inventory Costs and Variety Benefits in Retail Assortments, Management Science 45(11), 1999, p. 1503, text after Lemma 1

import Mathlib
import Definitions.Def_RetailVariety_Fashion_Lemma1Functions

namespace RetailVariety.Fashion

/-- p. 1503, after Lemma 1: `h(0) = π(S, v)` and `h(v_j) = π(S ∪ {j}, v)` for `j ∉ S`, for both
profit functions. The independent-model identities need `0 < β` (with `β = 0`, `0^β = 1`). -/
theorem h_endpoints {n : ℕ} (p c lam σ β v0 : ℝ) (hc : 0 < c) (hcp : c < p) (hlam : 0 < lam)
    (hσ : 0 < σ) (hβ0 : 0 < β) (hβ1 : β < 1) (hv0 : 0 < v0)
    (v : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j) (S : Finset (Fin n)) (j : Fin n) (hj : j ∉ S) :
    hI p c lam σ β v v0 S 0 = profitI p c lam σ β v v0 S ∧
      hI p c lam σ β v v0 S (v j) = profitI p c lam σ β v v0 (insert j S) ∧
      hT p c lam v v0 S 0 = profitT p c lam v v0 S ∧
      hT p c lam v v0 S (v j) = profitT p c lam v v0 (insert j S) := by sorry

end RetailVariety.Fashion
