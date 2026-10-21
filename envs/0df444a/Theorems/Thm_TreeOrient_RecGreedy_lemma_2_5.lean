-- Prove2me | Theorems.Thm_TreeOrient_RecGreedy_lemma_2_5
-- name    : TreeOrient.RecGreedy.lemma_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:34.595304+00:00
-- url     : https://prove2.me/theorems/8dd39ca5-3c20-4263-8ccd-e01148bb38db
-- title:
--   Lemma 2.5 — recursive greedy attains a 1/i marginal-value approximation
-- statement:
--   Let $f$ be a monotone submodular reward and let $A$ be an $r$-rooted arborescence that visits every responsibility in $Y$, costs at most $B$, and has at most $(3/2)^i$ non-root vertices. For $i\ge1$, recursive greedy returns a feasible edge set $T$ satisfying
--
--   $$f_X(A)\le i\,f_X(T).$$
--
--   The returned edge set contains a rooted arborescence on the same vertices. This is the basic approximation guarantee for Algorithm 1, from which the improved algorithms retain their value bound.
--
--   **Formalization Note** The reward is natural-valued. The corrected algorithm guesses zero budgets and propagates infeasibility; its output is required to reach each selected vertex and obey the budget. The marginal $f_X$ is real-valued.
-- source:
--   Ghuge & Nagarajan, arXiv:1812.01768v2, p. 6 (PDF 7), Lemma 2.5

import Mathlib
import Definitions.Def_TreeOrient_RecGreedy_Model

namespace TreeOrient.RecGreedy

/-- Lemma 2.5, p. 6 (PDF 7), for the zero-budget and infeasibility repairs. -/
theorem lemma_2_5 {n : ℕ} (I : Inst n) (r : Fin n)
    (Y X : Finset (Fin n)) (B i : ℕ) (A : Edges n)
    (hmono : IsMonotone I.f)
    (hsub : NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ)))
    (hi : 1 ≤ i)
    (hA : Compatible I.c r Y B ((3 / 2 : ℝ) ^ i) A) :
    ∃ T, (rg I 1 .enum i r Y B X).1 = some T ∧
      Feasible I.c r Y B T ∧
      (∃ A' : Edges n, A' ⊆ T ∧ IsArbo r A' ∧ verts r A' = verts r T) ∧
      fX I.f X r A ≤ (i : ℝ) * fX I.f X r T := by sorry

end TreeOrient.RecGreedy
