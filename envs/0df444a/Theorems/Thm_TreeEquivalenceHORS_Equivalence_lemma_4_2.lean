-- Prove2me | Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_4_2
-- name    : TreeEquivalenceHORS.Equivalence.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:14.463743+00:00
-- url     : https://prove2.me/theorems/f9afd57a-d908-407c-a3b9-22eda4cf43c1
-- title:
--   Lemma 4.2 (Control correspondence): $M\!\downarrow\iff\exists v\in C_M\,[\mathrm{pc}_M(v)\notin I_M\wedge W_M(v)\ne0]$
-- statement:
--   For every two-counter program $M$ (including the empty one),
--   $$M\!\downarrow\iff\exists v\in C_M\,\bigl[\mathrm{pc}_M(v)\notin I_M\wedge W_M(v)\ne0\bigr],$$
--   where $M\!\downarrow$ is halting from $(1,0,0)$ under the source step relation.
--
--   This identifies source halting with a halting candidate of nonzero weight, the event the two compiled schemes disagree on.
--
--   Differences from the source:
--   - encoding: candidate words over {1, 2}; virtual configurations in ℕ × ℤ² → `List Choice` with `Choice.one` = 1, `Choice.two` = 2, read left to right; configurations `ℕ × ℤ × ℤ`; δ (undefined outside I_M) returns its argument there; reason: the value of δ outside I_M is never used on candidates, which extend only active prefixes
-- source:
--   Mingkun Xiao, Yixuan Sun, Tree Equivalence of Higher-Order Recursion Schemes Is Undecidable, STOC 2027 submission #421 (October 2026), source.pdf SHA-256 e875d09ced029e3f5cb114abba049e4a2b1bdaa9b064c98b0d71f2ec7451c7af, Lemma 4.2, printed p. 13 / PDF p. 15

import Mathlib
import Definitions.Def_TreeEquivalenceHORS_Equivalence_Machines

namespace TreeEquivalenceHORS.Equivalence

/-- **Lemma 4.2 (Control correspondence)** (printed p. 13 / PDF p. 15).
`M↓ ⟺ ∃ v ∈ C_M, pc_M(v) ∉ I_M ∧ W_M(v) ≠ 0`. -/
theorem lemma_4_2 (M : Machine) :
    M.Halts ↔ ∃ v : List Choice, M.IsCand v ∧ ¬ M.Active (M.pc v) ∧ M.weight v ≠ 0 := by sorry

end TreeEquivalenceHORS.Equivalence
