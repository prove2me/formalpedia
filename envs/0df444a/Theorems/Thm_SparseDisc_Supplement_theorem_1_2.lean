-- Prove2me | Theorems.Thm_SparseDisc_Supplement_theorem_1_2
-- name    : SparseDisc.Supplement.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:07:12.864944+00:00
-- url     : https://prove2.me/theorems/a6d20be1-8ef6-46ea-9b5d-095380f9b75c
-- title:
--   Theorem 1.2 — exact values $K_1$ through $K_4$
-- statement:
--   Let $K_n$ be the supremum of the discrepancies of all finite instances with $n$ arbitrary odd $2$-Lipschitz functions. Then
--   $$
--   K_1=1,\qquad K_2=K_3=2,\qquad K_4=3.
--   $$
--   The upper bounds $K_3\le2$ and $K_4\le3$ are computer-assisted and use exact arithmetic. These values provide the sharp benchmark used by the acyclic-pattern theorems.
--
--   Differences from the source:
--   - encoding: $K_n$ is the supremum over finite instances with any positive number of items → `K n` is a real `sSup` of finite-instance discrepancies, each expressed as the `sInf` of attainable thresholds; reason: Lean representation preserves both suprema and does not assume attainment
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 1.2, p.3

import Mathlib
import Definitions.Def_SparseDisc_Supplement_K

namespace SparseDisc.Supplement

/-- **Theorem 1.2** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), p.3). The exact worst discrepancies of one
through four arbitrary 1-Lipschitz functions are `K₁ = 1`, `K₂ = K₃ = 2`, and `K₄ = 3`.
The upper bounds for `K₃` and `K₄` are computer-assisted and use exact arithmetic. -/
theorem theorem_1_2 :
    K 1 = 1 ∧ K 2 = 2 ∧ K 3 = 2 ∧ K 4 = 3 := by sorry

end SparseDisc.Supplement
