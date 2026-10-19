-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Information100_P23_completelyDephasingAttains
-- name    : QAlgorithms.Papers.Independent.Information100.P23.completelyDephasingAttains
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T10:10:42.057669+00:00
-- url     : https://prove2.me/theorems/9ca61e04-a0ba-40ac-bc34-a4171355cfe8
-- title:
--   Proposition 2 (§4): completely dephasing attains the bound
-- statement:
--   Let $d\ge1$ and fix any normalized traceless Hermitian Bloch basis as above. On all matrices define $\Delta(X)=\sum_{k=1}^{d}X_{kk}|k\rangle\langle k|$. This map is completely positive, trace preserving, and entanglement breaking. It is exactly the map that deletes off-diagonal entries. Its computed Bloch data satisfy
--
--   $$c=0,\qquad\|A\|_*=d-1,\qquad\|A\|_*^2+\frac{d(d-1)}2|c|^2=(d-1)^2.$$
--
--   Thus the inequality is attained in every positive dimension, independently of whether the chosen Bloch basis contains diagonal generators.
-- source:
--   A sharp norm inequality for entanglement-breaking channels, arXiv:2609.27906v1, PDF p. 3, Proposition 2 (§4): completely dephasing attains the bound

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P23

noncomputable section

open scoped Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Information100.P23

/-- Proposition 2, PDF p.3: computational dephasing is CPTP, EB and unital,
and attains Theorem 1 in every positive dimension and every normalized Bloch basis. -/
theorem completelyDephasingAttains {d : ℕ} (hd : 1 ≤ d) (B : BlochBasis d) :
    IsCPTP (completelyDephasing d) ∧
    Entanglement.IsEntanglementBreakingPositive (completelyDephasing d) ∧
    (∀ X : Operator d, completelyDephasing d X = Matrix.diagonal (fun k => X k k)) ∧
    blochC B (completelyDephasing d) = 0 ∧
    nuclearNorm (blochA B (completelyDephasing d)) = (d : ℝ) - 1 ∧
    nuclearNorm (blochA B (completelyDephasing d)) ^ 2 +
      ((d : ℝ) * ((d : ℝ) - 1) / 2) * vectorNorm (blochC B (completelyDephasing d)) ^ 2 =
        ((d : ℝ) - 1) ^ 2 := by sorry

end QAlgorithms.Papers.Independent.Information100.P23

end
