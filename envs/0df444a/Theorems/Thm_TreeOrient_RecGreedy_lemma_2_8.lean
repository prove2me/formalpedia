-- Prove2me | Theorems.Thm_TreeOrient_RecGreedy_lemma_2_8
-- name    : TreeOrient.RecGreedy.lemma_2_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:28.833675+00:00
-- url     : https://prove2.me/theorems/43e44e05-38f0-45c8-9bd7-7ef70c503184
-- title:
--   Lemma 2.8 — binary-search recursive greedy retains the 1/i ratio
-- statement:
--   Under the same monotonicity, submodularity and compatibility conditions as Lemma 2.5, let $U$ be a nonnegative integer upper bound on the benchmark marginal value $f_X(A)$. Then the binary-search recursive greedy algorithm returns a feasible edge set $T$ such that
--
--   $$f_X(A)\le i\,f_X(T).$$
--
--   The returned edge set contains a rooted arborescence on the same vertices. The lemma preserves the approximation factor while replacing enumeration of every budget by value-threshold searches.
--
--   **Formalization Note** The value oracle is integer-valued, as required by the ceiling threshold in the appendix proof. Search includes zero budgets and thresholds, and every probe is counted as a recursive call.
-- source:
--   Ghuge & Nagarajan, arXiv:1812.01768v2, p. 8 (PDF 9), Lemma 2.8; proof pp. 17–18 (PDF 18–19)

import Mathlib
import Definitions.Def_TreeOrient_RecGreedy_Model

namespace TreeOrient.RecGreedy

/-- Lemma 2.8, p. 8 (PDF 9), with the integer threshold used in its appendix proof. -/
theorem lemma_2_8 {n : ℕ} (I : Inst n) (r : Fin n)
    (Y X : Finset (Fin n)) (B i U : ℕ) (A : Edges n)
    (hmono : IsMonotone I.f)
    (hsub : NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ)))
    (hi : 1 ≤ i)
    (hA : Compatible I.c r Y B ((3 / 2 : ℝ) ^ i) A)
    (hU : fX I.f X r A ≤ (U : ℝ)) :
    ∃ T, (rg I 1 (.bsearch U) i r Y B X).1 = some T ∧
      Feasible I.c r Y B T ∧
      (∃ A' : Edges n, A' ⊆ T ∧ IsArbo r A' ∧ verts r A' = verts r T) ∧
      fX I.f X r A ≤ (i : ℝ) * fX I.f X r T := by sorry

end TreeOrient.RecGreedy
