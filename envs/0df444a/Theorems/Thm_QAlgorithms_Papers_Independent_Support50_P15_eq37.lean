-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_eq37
-- name    : QAlgorithms.Papers.Independent.Support50.P15.eq37
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:44:58.258855+00:00
-- url     : https://prove2.me/theorems/67ba2e9f-90bf-410e-b15f-ed38f96550a6
-- title:
--   eq37
-- statement:
--   Let $k\ge1$ and let $\rho_0,\ldots,\rho_k$ be normalized states in a common positive finite dimension. No common-support assumption is needed. Writing $\|\cdot\|_1$ for the trace norm,
--
--   $$\sum_{j=1}^kD(\rho_{j-1}\|\rho_j)\ge\frac12\sum_{j=1}^k\|\rho_{j-1}-\rho_j\|_1^2\ge\frac{1}{2k}\left(\sum_{j=1}^k\|\rho_{j-1}-\rho_j\|_1\right)^2\ge\frac{\|\rho_0-\rho_k\|_1^2}{2k}.$$
--
--   Support failures give infinity on the left. This retains the full intermediate chain and supplies an endpoint-distance lower bound even when the entropy change vanishes.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 12, eq37

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Eq. (37), PDF p.12, with every intermediate term and no unnecessary full-rank premise. -/
theorem eq37 {d k : ℕ} (hd : 0 < d) (hk : 0 < k) (a : Fin (k + 1) → EntropyState d) :
    let total := ∑ j : Fin k, stateRelativeNats (a j.castSucc) (a j.succ)
    let sq : ℝ := ∑ j : Fin k, (traceNorm ((a j.castSucc).val - (a j.succ).val)) ^ 2 / 2
    let av : ℝ := (k : ℝ) / 2 * (∑ j : Fin k,
      traceNorm ((a j.castSucc).val - (a j.succ).val) / k) ^ 2
    (sq : EReal) ≤ total ∧ av ≤ sq ∧
    (traceNorm ((a 0).val - (a (Fin.last k)).val)) ^ 2 / (2 * (k : ℝ)) ≤ av := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
