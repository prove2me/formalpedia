-- Prove2me | Theorems.Thm_PrimalDualPricing_Regret_lemma_2
-- name    : PrimalDualPricing.Regret.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:20:41.515655+00:00
-- url     : https://prove2.me/theorems/58a512e5-e107-416c-8e33-fe2ab06c3764
-- title:
--   Lemma 2, p. 14 — $\sum_{k=1}^{K-1}\tau^{(k)}\le T/2$ for $n\ge\exp((8/T)^{1/\epsilon})$
-- statement:
--   Let $\epsilon>0$, $T>0$, and let $n\ge3$ satisfy $n\ge\exp\big((8/T)^{1/\epsilon}\big)$. Then the total length of the phases before the last phase $K$ satisfies
--   $$\sum_{k=1}^{K-1}\tau^{(k)}\le\frac T2,\qquad \tau^{(k)}=n^{-\frac12(3/5)^{k-1}}(\log n)^{1+15\epsilon}.$$
--
--   The last phase therefore takes at least half of the season.
--
--   **Formalization Note** The page states the threshold $n\ge\exp((8/T)^{1/\epsilon})$ only. The condition $n\ge3$ is added because $K$ is defined only for $n\ge3$.
-- source:
--   Chen, Gallego, A Primal-dual Learning Algorithm for Personalized Dynamic Pricing with an Inventory Constraint, arXiv:1812.09234v3, p. 14, Lemma 2 (parameters p. 13)

import Mathlib
import Definitions.Def_PrimalDualPricing_Regret_Params

namespace PrimalDualPricing.Regret

/-- Lemma 2 (Chen–Gallego, arXiv:1812.09234v3, p. 14). For `ε > 0`, `T > 0` and `n ≥ 3` with
`n ≥ exp((8/T)^{1/ε})`, the total length of the phases before phase `K` satisfies
`∑_{k=1}^{K−1} τ^{(k)} ≤ T/2`. (`n ≥ 3` is added: below it `K` is undefined.) -/
theorem lemma_2 (eps T : ℝ) (heps : 0 < eps) (hT : 0 < T) (n : ℕ) (hn : 3 ≤ n)
    (hn' : Real.exp ((8 / T) ^ (1 / eps)) ≤ n) :
    ∑ k ∈ Finset.Ico 1 (numPhases eps n), tau eps n k ≤ T / 2 := by sorry

end PrimalDualPricing.Regret
