-- Prove2me | Theorems.Thm_PolyVoting_proposition_2_ii
-- name    : PolyVoting.proposition_2_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:50:20.344905+00:00
-- url     : https://prove2.me/theorems/c3fcce0d-1221-457b-b0d9-4f05c00c2a98
-- title:
--   Proposition 2 (ii), (2.7) — $N_t^{1+\alpha}/t\to1+\alpha$ in probability
-- statement:
--   Under the Poly($\alpha$) voting rule, there is the convergence in probability
--   $$\frac{N_t^{1+\alpha}}{t}\longrightarrow 1+\alpha\quad\text{as }t\to\infty.$$
--
--   So the volume grows as $((1+\alpha)t)^{1/(1+\alpha)}$, which fixes the time scale of the voting power in Theorem 6.
--
--   Differences from the source:
--   - encoding: the Poly(α) rule described by (2.3)–(2.6), K ∈ ℕ₊ bidders, stakes n_{k,t} → `Model μ K α n₀`: the joint conditional one-step law, stakes in Fin K → ℕ, real α ≥ 0 with Real.rpow, and 1 ≤ N; reason: the conditional one-step law and n₀ determine the law of the chain; 1 ≤ N only keeps N_t^{−α} defined
-- source:
--   Tang & Yao, Polynomial Voting Rules, arXiv:2206.10105v5, Proposition 2 (ii), display (2.7), p.6

import Mathlib
import Definitions.Def_PolyVoting_Model

open MeasureTheory Filter

namespace PolyVoting

/-- **Proposition 2 (ii), display (2.7)** (Tang & Yao, *Polynomial Voting Rules*,
arXiv:2206.10105v5, p.6): `N_t ^ (1 + α) / t → 1 + α` in probability as `t → ∞`. -/
theorem proposition_2_ii {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {K : ℕ} {α : ℝ} {n₀ : Fin K → ℕ} (M : Model μ K α n₀) :
    TendstoInMeasure μ (fun (t : ℕ) ω => (M.total t ω : ℝ) ^ (1 + α) / (t : ℝ)) atTop
      (fun _ => 1 + α) := by sorry

end PolyVoting
