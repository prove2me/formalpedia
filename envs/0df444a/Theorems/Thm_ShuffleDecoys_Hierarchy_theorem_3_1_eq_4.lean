-- Prove2me | Theorems.Thm_ShuffleDecoys_Hierarchy_theorem_3_1_eq_4
-- name    : ShuffleDecoys.Hierarchy.theorem_3_1_eq_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:23:31.353202+00:00
-- url     : https://prove2.me/theorems/faef9179-2c98-4397-9715-78066a2f0825
-- title:
--   Theorem 3.1, bound (4) — every message-oblivious mechanism leaks I(M; Z) ≥ 2v(P)/n², v(P) = max_{E ⊆ supp P} P(E)(1 − P(E))
-- statement:
--   Let $P$ be a non-degenerate distribution with finite support, $v(P):=\max_{E\subseteq\operatorname{supp}(P)}P(E)(1-P(E))$, and $n\ge2$. Every message-oblivious mechanism (the $n-1$ decoys have one joint law, independent of $M\sim P$, with arbitrary internal correlation) satisfies
--   $$I(M;Z)\ \ge\ \frac{2v(P)}{n^2}$$
--   for the uniformly shuffled release $Z$. This is the clause of Theorem 3.1 that Theorem B.1 uses: correlated message-oblivious decoys cannot beat order $n^{-2}$.
--
--   Differences from the source:
--   - generalization: the alphabet is $\operatorname{supp}(P)$, of size $d\ge2$ → any finite alphabet $Y$ containing the support, decoys taking values in $Y$, and $P$ any law on $Y$ with $P(y)\ne1$ for all $y$; reason: taking $Y=\operatorname{supp}(P)$ gives the printed statement, and the paper itself applies (4) in Appendix B.9 to a prior supported on a pair inside $[d]$.
--   - encoding: message-oblivious mechanism → kernel in `oblClass` (one decoy law for all messages); reason: $H\perp M$ is exactly this.
-- source:
--   Su, Cheng, Wang, The Information-Theoretic Limits of Hiding Among Decoys in the Shuffle Model, STOC 2027 submission (manuscript sha256 445baceb…), p. 15, Theorem 3.1, Eq. (4)

import Mathlib
import Definitions.Def_ShuffleDecoys_Hierarchy_Info
import Definitions.Def_ShuffleDecoys_Hierarchy_Model

open scoped ENNReal

namespace ShuffleDecoys.Hierarchy

/-- Theorem 3.1, bound (4): for a non-degenerate prior `P` on a finite alphabet `Y` and every
`n ≥ 2`, every message-oblivious mechanism leaks `I(M; Z) ≥ 2v(P)/n²`, where
`v(P) = max_{E ⊆ supp(P)} P(E)(1 − P(E))`. -/
theorem theorem_3_1_eq_4 {Y : Type*} [Fintype Y] (P : PMF Y) (hP : ∀ y, P y ≠ 1) (n : ℕ)
    (hn : 2 ≤ n) (R : DecoyKernel Y n) (hR : R ∈ oblClass Y n) :
    ENNReal.ofReal (2 * vP P / (n : ℝ) ^ 2) ≤ leakage P R := by sorry

end ShuffleDecoys.Hierarchy
