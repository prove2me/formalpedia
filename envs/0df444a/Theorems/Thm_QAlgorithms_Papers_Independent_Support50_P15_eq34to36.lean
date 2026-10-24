-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P15_eq34to36
-- name    : QAlgorithms.Papers.Independent.Support50.P15.eq34to36
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:44:06.567375+00:00
-- url     : https://prove2.me/theorems/77e40952-85c0-4075-87ee-7b2d66c7c157
-- title:
--   eq34 36
-- statement:
--   Let $d\ge2$, $k\ge1$, and let $\rho_0,\ldots,\rho_k$ be normalized full-rank states on the fixed support of the thermodynamic section. Set $\Delta S=S(\rho_k)-S(\rho_0)$ and $L=\sum_{j=1}^kD(\rho_{j-1}\|\rho_j)$. Then
--
--   $$L\ge\sum_{j=1}^k M(S(\rho_{j-1})-S(\rho_j),d)\ge kM(-\Delta S/k,d)\ge\frac{(\Delta S)^2}{3k\log^2d}.$$
--
--   The middle step is the comparison with $k$ times the value at the average of the individual differences; the sum also equals $k$ times its arithmetic mean. Consequently $L\le\varepsilon$, with $\varepsilon>0$, requires $k\ge(\Delta S)^2/(3\varepsilon\log^2d)$. This keeps the relative-entropy argument order and the exact necessary step bound, correcting the direction of the source's informal big-O sentence.
-- source:
--   Tight bound on relative entropy by entropy difference, arXiv:1304.0036v3, PDF p. 11, eq34-36

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P15

noncomputable section

attribute [local instance] Classical.propDecidable

open scoped Matrix ComplexConjugate ENNReal Matrix.Norms.L2Operator

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Support50.P15

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

/-- Eqs. (34)--(36), PDF pp.11--12, on the fixed support of the thermodynamic section.
The sign is -DeltaS. The p.12 prose k=O(1/epsilon) has the wrong direction;
the last clause instead states the exact necessary lower bound supplied by (36). -/
theorem eq34to36 {d k : ℕ} (hd : 2 ≤ d) (hk : 0 < k) (a : Fin (k + 1) → EntropyState d)
    (ha : ∀ j, fullRank (a j).val) :
    let ds := entropy (a (Fin.last k)).val - entropy (a 0).val
    let total := ∑ j : Fin k, stateRelativeNats (a j.castSucc) (a j.succ)
    let terms := ∑ j : Fin k, tightBound d (difference (a j.castSucc).val (a j.succ).val)
    terms ≤ total ∧
    terms = (k : EReal) * ∑ j : Fin k,
      (((1 / (k : ℝ)) : ℝ) : EReal) * tightBound d (difference (a j.castSucc).val (a j.succ).val) ∧
    (k : EReal) * tightBound d (∑ j : Fin k,
      difference (a j.castSucc).val (a j.succ).val / k) ≤ terms ∧
    (k : EReal) * tightBound d (∑ j : Fin k,
      difference (a j.castSucc).val (a j.succ).val / k) =
        (k : EReal) * tightBound d (-ds / k) ∧
    (ds ^ 2 / ((k : ℝ) * (3 * (Real.log d) ^ 2)) : ℝ) ≤
      (k : EReal) * tightBound d (-ds / k) ∧
    (∀ e > 0, total ≤ (e : EReal) → ds ^ 2 / (3 * (Real.log d) ^ 2 * e) ≤ (k : ℝ)) := by sorry

end QAlgorithms.Papers.Independent.Support50.P15

end
