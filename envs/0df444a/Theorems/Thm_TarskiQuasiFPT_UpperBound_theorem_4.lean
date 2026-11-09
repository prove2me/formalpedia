-- Prove2me | Theorems.Thm_TarskiQuasiFPT_UpperBound_theorem_4
-- name    : TarskiQuasiFPT.UpperBound.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:40:56.640201+00:00
-- url     : https://prove2.me/theorems/4e1d5335-940a-4a5b-982a-8f379cc085b0
-- title:
--   Theorem 4 ([CLY23, CLY26]) — $\mathrm{Tarski}^*(n,k)=\mathrm{SafeTarski}^*(n,k)$
-- statement:
--   For all $n,k\ge1$,
--   $$\mathrm{Tarski}^*(n,k)=\mathrm{SafeTarski}^*(n,k).$$
--
--   Promising that the input is safe does not lower the deterministic query complexity of Tarski$^*$, so algorithms for SafeTarski$^*$ give algorithms for Tarski$^*$. The result is cited from [CLY23, CLY26] and used in Appendix A.
--
--   Differences from the source:
--   - encoding: grid [n]^k = {1,…,n}^k with the coordinatewise order → Point n k = Fin k → Fin n (values 0,…,n−1) with the pointwise order; reason: shifting every coordinate by one is an order isomorphism; no instance changes
--   - encoding: labels in {±1} with −1 < +1; positive solution (x,0) ⪯ f(x), negative solution f(x) ⪯ (x,0) → Label = {neg < pos}; IsPosSolution f x := x ⪯ (f x).1 ∧ (f x).2 = pos, IsNegSolution f x := (f x).1 ⪯ x ∧ (f x).2 = neg; reason: 0 lies strictly between −1 and +1, so 0 ≤ label iff label = +1 and label ≤ 0 iff label = −1
--   - encoding: deterministic query complexity: the minimum worst-case number of queries → sInf in ℕ of the bounds d achieved by some decision tree on every input of the class; reason: for n ≥ 1 the set is nonempty (query every point), so the infimum is the attained minimum
-- source:
--   Chen, Gao, Li, Rubinstein, Yannakakis, Tarski Fixed Points in Quasi-FPT Queries, STOC 2027 submission #403 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/403.pdf, SHA-256 6a2841836f544481cc4548db5ea0222917f43c713b7a292c9947be9c149b9cd6, Theorem 4, PDF p. 5 (printed p. 4); cited from [CLY23, CLY26]

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_TarskiQuasiFPT_UpperBound_Grid
import Definitions.Def_TarskiQuasiFPT_UpperBound_QueryComplexity

set_option autoImplicit false

open QAlgorithms

namespace TarskiQuasiFPT.UpperBound

/-- Theorem 4 ([CLY23, CLY26]; PDF p. 5): for every `n, k ≥ 1`,
`Tarski*(n, k) = SafeTarski*(n, k)`. -/
theorem theorem_4 (n k : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k) :
    tarskiStarQC n k = safeTarskiStarQC n k := by sorry

end TarskiQuasiFPT.UpperBound
