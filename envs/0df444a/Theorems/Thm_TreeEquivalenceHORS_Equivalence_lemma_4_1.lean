-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_4_1
-- name    : TreeEquivalenceHORS.Equivalence.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:06.215093+00:00
-- url     : https://prove2.me/theorems/01d08f90-4c66-4565-a95e-c1defef29337
-- title:
--   Lemma 4.1 (Witness invariant): $W_M(v)\ne0\iff v\in L_M$ for every candidate $v\in C_M$
-- statement:
--   Let $M$ be a two-counter program and $v\in C_M$ a finite candidate prefix, with guard weight $W_M(v)$ (Equation (13)). Then
--   $$W_M(v)\ne0\iff v\in L_M,$$
--   that is, the weight is nonzero exactly when every guessed guard along $v$ is correct. Illegal candidates, including those whose virtual counters have become negative, have weight zero.
--
--   This is the first-error argument that lets the compiled trees detect illegal guesses arithmetically.
--
--   Differences from the source:
--   - encoding: candidate words over {1, 2}; virtual configurations in ℕ × ℤ² → `List Choice` with `Choice.one` = 1, `Choice.two` = 2, read left to right; configurations `ℕ × ℤ × ℤ`; δ (undefined outside I_M) returns its argument there; reason: the value of δ outside I_M is never used on candidates, which extend only active prefixes
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Lemma 4.1, printed p. 13 / PDF p. 15

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Machines

namespace TreeEquivalenceHORS.Equivalence

/-- **Lemma 4.1 (Witness invariant)** (printed p. 13 / PDF p. 15). For every candidate prefix
`v ∈ C_M`, the guard weight is nonzero exactly on legal prefixes: `W_M(v) ≠ 0 ⟺ v ∈ L_M`. -/
theorem lemma_4_1 (M : Machine) (v : List Choice) (hv : M.IsCand v) :
    M.weight v ≠ 0 ↔ M.IsLegal v := by sorry

end TreeEquivalenceHORS.Equivalence
