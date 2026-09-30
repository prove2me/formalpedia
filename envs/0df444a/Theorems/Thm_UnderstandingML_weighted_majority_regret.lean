-- Prove2me | Theorems.Thm_UnderstandingML_weighted_majority_regret
-- name    : UnderstandingML.weighted_majority_regret
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T05:13:28.518858+00:00
-- url     : https://prove2.me/theorems/934e3954-a441-4623-a190-0069be857aec
-- title:
--   Theorem 21.11: for T > 2 log d and η = √(2 log(d)/T), Weighted-Majority pays ∑ₜ⟨w⁽ᵗ⁾, vₜ⟩ ≤ minᵢ ∑ₜ vₜ,ᵢ + √(2 log(d) T)
-- statement:
--   **Theorem 21.11.** Assuming that $T > 2\log(d)$, the Weighted-Majority algorithm enjoys the bound
--   $$\sum_{t=1}^T \langle w^{(t)}, v_t\rangle - \min_{i \in [d]}\sum_{t=1}^T v_{t,i} \le \sqrt{2\log(d)\,T}.$$
--
--   Formally: $d \ge 1$ experts, costs $v_t \in [0,1]^d$, $\eta = \sqrt{2\log(d)/T}$, rounds indexed from $0$, and $w^{(t)}_i \propto \exp(-\eta\sum_{s<t}v_{s,i})$ (the unrolled update rule).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §21.2.1 p. 296, Theorem 21.11

import Definitions.Def_UnderstandingML_Online

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-- **Theorem 21.11** (p. 296). Assuming that `T > 2 log(d)`, the Weighted-Majority algorithm
with `η = √(2 log(d)/T)` enjoys the bound
`∑_{t=1}^T ⟨w⁽ᵗ⁾, vₜ⟩ − min_{i ∈ [d]} ∑_{t=1}^T v_{t,i} ≤ √(2 log(d) T)`,
for every sequence of cost vectors `vₜ ∈ [0,1]^d`. Rounds indexed from `0`; `d ≥ 1`. -/
theorem weighted_majority_regret (d : ℕ) (hd : 0 < d) (T : ℕ) (hT : 2 * Real.log d < T)
    (v : ℕ → Fin d → ℝ) (hv : ∀ t i, v t i ∈ Set.Icc (0 : ℝ) 1) :
    ∑ t ∈ Finset.range T, ∑ i, wmWeights (Real.sqrt (2 * Real.log d / T)) v t i * v t i -
      ⨅ i, ∑ t ∈ Finset.range T, v t i ≤ Real.sqrt (2 * Real.log d * T) := by sorry

end UnderstandingML
