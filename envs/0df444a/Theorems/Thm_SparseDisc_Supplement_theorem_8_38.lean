-- Prove2me | Theorems.Thm_SparseDisc_Supplement_theorem_8_38
-- name    : SparseDisc.Supplement.theorem_8_38
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:15:58.240921+00:00
-- url     : https://prove2.me/theorems/d8eb6844-e522-4e22-bcd9-9d9513dd7ec2
-- title:
--   Theorem 8.38 — arbitrary-bundle square-root bound
-- statement:
--   Every finite $t$-sparse instance with $n$ functions and $t\ge2$ satisfies
--   $$
--   \operatorname{disc}(G)\le\sqrt{2\ln(2t)n}.
--   $$
--   In particular, for arbitrary bundle sizes, every $2$-sparse family of $n$ functions has the strict bound
--   $$
--   \operatorname{disc}(F)<1.666\sqrt n.
--   $$
--   The logarithm is natural, and the strict numerical consequence is retained rather than rounded.
--
--   Differences from the source:
--   - encoding: a non-strict instance discrepancy bound and a strict family consequence → the first uses `InstDiscLE`, while the second explicitly exhibits a colouring satisfying strict inequalities for every function; reason: preserves the different inequality strengths exactly
--   - encoding: a positive number $n$ of functions and natural logarithm → `n` is the cardinality of a finite nonempty type and `Real.log` is applied to the positive argument $2t$ under $t\ge2$; reason: Lean convention and explicit guards for the paper's positive $n$ and logarithm domain
-- source:
--   Zeng–Cao–Dai–Wang–Liao, Sparse Discrepancy Beyond Additive Functions, STOC 2027 submission (manuscript sha256 0f09ec60…), Theorem 8.38, p.47

import Mathlib
import Definitions.Def_SparseDisc_IsInstance
import Definitions.Def_SparseDisc_InstDiscLE
import Definitions.Def_SparseDisc_IsOneLipschitz
import Definitions.Def_SparseDisc_IsTwoSparse
import Definitions.Def_SparseDisc_Supplement_IsTSparseSupp

namespace SparseDisc.Supplement

/-- **Theorem 8.38** (Zeng–Cao–Dai–Wang–Liao, *Sparse Discrepancy Beyond Additive Functions*, STOC
2027 submission manuscript (sha256 0f09ec60…25b81), p.47). Every `t`-sparse instance with `n`
functions, `t≥2`, has discrepancy at most `sqrt(2 ln(2t) n)`; every 2-sparse family has the
strict bound `1.666 sqrt(n)` for arbitrary bundle sizes.

**Formalization Note** `Real.log` is the natural logarithm. Its argument is positive because
`t≥2`. The function type is nonempty, matching the paper's positive `n` (and the proof's use of
division by `n`). The strict family conclusion is represented by a colouring satisfying strict
inequalities, not by the non-strict `DiscLE` predicate. -/
theorem theorem_8_38 :
    (∀ (t : ℕ), 2 ≤ t → ∀ (V ι : Type) [Fintype V] [DecidableEq V]
      [Nonempty V] [Fintype ι] [DecidableEq ι] (g : V → SparseDisc.Cube ι → ℝ)
      (U : V → Finset ι), SparseDisc.IsInstance g U → IsTSparseSupp t U →
      SparseDisc.InstDiscLE g
        (Real.sqrt (2 * Real.log (2 * t) * Fintype.card V))) ∧
    (∀ (V ι : Type) [Fintype V] [DecidableEq V] [Nonempty V] [Fintype ι] [DecidableEq ι]
      (f : V → Finset ι → ℝ), (∀ v, SparseDisc.IsOneLipschitz (f v)) →
      SparseDisc.IsTwoSparse f → ∃ S : Finset ι, ∀ v,
        |f v S - f v (Finset.univ \ S)| < 1.666 * Real.sqrt (Fintype.card V)) := by sorry

end SparseDisc.Supplement
