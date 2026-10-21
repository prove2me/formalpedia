-- Prove2me | Theorems.Thm_VWAPContract_Optimal_lemma_3_volume_shares
-- name    : VWAPContract.Optimal.lemma_3_volume_shares
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:48:52.626748+00:00
-- url     : https://prove2.me/theorems/2ce229d5-197e-4eed-ac98-c381c2bd8fa0
-- title:
--   Lemma 3, p. 21 (PDF 22) — $x^{FB}_t(\eta)=v(x^{FB}_t(\eta),\eta_t)/\sum_s v(x^{FB}_s(\eta),\eta_s)$
-- statement:
--   Let $v$ be a function with $v(x,\eta)>0$ for $x\ge0,\ \eta>0$ and $v(x,\eta)=x\,V(x/\eta)$ for $x>0$. For every positive vector $\eta=(\eta_1,\dots,\eta_T)$ and every $t$,
--
--   $$x^{FB}_t(\eta)=\frac{v\big(x^{FB}_t(\eta),\eta_t\big)}{\sum_{s=1}^T v\big(x^{FB}_s(\eta),\eta_s\big)},\qquad x^{FB}_t(\eta)=\frac{\eta_t}{\sum_{s=1}^T\eta_s}.$$
--
--   A dealer who follows the first-best schedule trades each period exactly its share of total market volume, so the realized trading cost $p\cdot x^{FB}(\eta)$ equals the realized market VWAP.
--
--   **Formalization Note** Deterministic, for every number of periods; only the positivity and the multiplicative form of $v$ are assumed.
-- source:
--   Baldauf, Frei & Mollner, Principal trading arrangements: When are common contracts optimal?, working paper of August 8, 2020 (published Management Science 2022, DOI 10.1287/mnsc.2021.4022), p. 21 (PDF 22), Lemma 3, last sentence; proof p. 50 (PDF 51)

import Mathlib
import Definitions.Def_VWAPContract_Optimal_Model
open MeasureTheory

namespace VWAPContract.Optimal

theorem lemma_3_volume_shares
    (vol : ℝ → ℝ → ℝ) (V : ℝ → ℝ)
    (hvpos : ∀ x e, 0 ≤ x → 0 < e → 0 < vol x e)
    (hvform : ∀ x e, 0 < x → 0 < e → vol x e = x * V (x / e)) :
    ∀ (n : ℕ) (e : Fin n → ℝ), (∀ t, 0 < e t) → ∀ t,
      xFB e t = vol (xFB e t) (e t) / ∑ s, vol (xFB e s) (e s) := by sorry

end VWAPContract.Optimal
