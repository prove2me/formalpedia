-- Prove2me | Theorems.Thm_TreeOrient_RecGreedy_lemma_2_10
-- name    : TreeOrient.RecGreedy.lemma_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:31.30199+00:00
-- url     : https://prove2.me/theorems/e02b4dc6-f004-418c-ae19-eaa152f79c8e
-- title:
--   Lemma 2.10 — grouped recursive greedy attains a 1/i ratio
-- statement:
--   At each improved recursion level, group $s\ge1$ levels of the basic structural guesses. Let $A$ be compatible with a call $(r,Y,B,X,i)$: it visits $Y$, costs at most $B$, and has at most $(3/2)^{si}$ non-root vertices. For a monotone submodular reward, the algorithm returns a feasible $T$ with
--
--   $$f_X(A)\le i\,f_X(T).$$
--
--   The returned edge set contains a rooted arborescence on the same vertices. The statement connects grouping of recursive levels to the improved approximation factor.
--
--   **Formalization Note** At grouped depth one the algorithm checks every feasible arborescence up to the paper's $(3/2)^s$ size cap, as its proof requires. The step count charges each enumerated edge tuple. The algorithm guesses zero budgets and propagates infeasibility.
-- source:
--   Ghuge & Nagarajan, arXiv:1812.01768v2, p. 8 (PDF 9), Lemma 2.10; proof pp. 8–9 (PDF 9–10)

import Mathlib
import Definitions.Def_TreeOrient_RecGreedy_Model

namespace TreeOrient.RecGreedy

/-- Lemma 2.10, p. 8 (PDF 9), for s grouped levels per recursion step. -/
theorem lemma_2_10 {n : ℕ} (I : Inst n) (r : Fin n)
    (Y X : Finset (Fin n)) (B s i : ℕ) (A : Edges n)
    (hmono : IsMonotone I.f)
    (hsub : NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ)))
    (hs : 1 ≤ s) (hi : 1 ≤ i)
    (hA : Compatible I.c r Y B (capImp s i) A) :
    ∃ T, (rg I s .enum i r Y B X).1 = some T ∧
      Feasible I.c r Y B T ∧
      (∃ A' : Edges n, A' ⊆ T ∧ IsArbo r A' ∧ verts r A' = verts r T) ∧
      fX I.f X r A ≤ (i : ℝ) * fX I.f X r T := by sorry

end TreeOrient.RecGreedy
