-- Prove2me | Theorems.Thm_WaitTimePricing_Existence_lemma_5
-- name    : WaitTimePricing.Existence.lemma_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T11:26:39.391242+00:00
-- url     : https://prove2.me/theorems/d2c84d48-7df6-4ca7-b334-f5161eec7420
-- title:
--   Lemma 5 — $K^{U'(0)}_N\equiv 0$ on $[0,\bar w+C]$
-- statement:
--   For every $N\ge1$, the slope adjustment of Algorithm 1 run with $g=U'(0)$ vanishes:
--   $$K^{U'(0)}_N(w)=0\qquad\text{for all } w\in[0,\bar w+C].$$
--
--   In particular $U'(0)$ is feasible in the definition (23) of $g_N$, which gives the upper bound $g_N\le U'(0)$.
--
--   **Formalization Note** "$N\in\mathbb N$" means $N\ge1$.
-- source:
--   Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 36, Lemma 5 (Appendix B, proof of Proposition 5)

import Mathlib
import Definitions.Def_WaitTimePricing_Existence_Setting
import Definitions.Def_WaitTimePricing_Existence_Algorithm1

namespace WaitTimePricing.Existence

open Set Filter

/-- Lin, Shang, Sun, Wait Time Based Pricing for Queues with Customer-Chosen Service Times, SSRN 3709573 (version of October 12, 2020), p. 36, Lemma 5 (stated in the proof of Proposition 5, Appendix B).

The slope adjustment `K^{U′(0)}_N(w) = 0` for all `w ∈ [0, w̄ + C]` and all `N ∈ ℕ`.

**Formalization Note.** `N ∈ ℕ` means `N ≥ 1`. -/
theorem lemma_5 (M : Model) (hM : M.Standing) (obj : Objective) :
    ∀ N : ℕ, 1 ≤ N → ∀ w ∈ Icc 0 (wbar M + M.C), KgN M obj (deriv M.U 0) N w = 0 := by sorry

end WaitTimePricing.Existence
