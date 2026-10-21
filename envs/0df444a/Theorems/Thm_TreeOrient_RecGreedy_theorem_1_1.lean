-- Prove2me | Theorems.Thm_TreeOrient_RecGreedy_theorem_1_1
-- name    : TreeOrient.RecGreedy.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:27:38.434541+00:00
-- url     : https://prove2.me/theorems/8b922e6c-713f-44cb-9d7c-0cd53e3f7b14
-- title:
--   Theorem 1.1 — a quasi-polynomial O(log k/log log k) approximation
-- statement:
--   Let $\varepsilon>0$, and let $a$ bound the polynomial size of an integer-valued monotone submodular reward: $f(S)\le n^a$ for every vertex set $S$. There is a constant $C>0$, depending only on $\varepsilon$ and $a$, such that for every instance on $n$ vertices and every $3\le k\le n$, the specified grouped recursive greedy algorithm with binary-search budget guesses returns a budget-feasible rooted solution $T$. For every feasible arborescence $A$ with at most $k$ vertices, including the root,
--
--   $$f(V(A))\le C\,\frac{\log k}{\log\log k}\,f(V(T)).$$
--
--   Its recorded number of steps is at most
--
--   $$\bigl(n\log_2(B+2)\bigr)^{C(\log k)^{1+\varepsilon}}.$$
--
--   Thus the approximation and quasi-polynomial runtime apply to a defined algorithm, with a uniform constant over instances. The returned reachable edge set contains a rooted arborescence on the same vertices.
--
--   **Formalization Note** The algorithm includes zero-budget guesses, infeasibility propagation, and a grouped depth-one search of all arborescences within the $(3/2)^s$ cap. The step count includes every recursive call and binary-search probe, each candidate value evaluation, and each grouped-base edge tuple. The shift $B+2$ keeps the logarithmic base positive for $B=0,1$; $k\ge3$ makes $\log\log k>0$. Integer reward and the explicit polynomial bound are needed by the value-threshold search. No triangle inequality is assumed.
-- source:
--   Ghuge & Nagarajan, arXiv:1812.01768v2, p. 1 (PDF 2), Theorem 1.1; §1.3 p. 4 (PDF 5), Algorithm 1 p. 5 (PDF 6), Algorithm 2 p. 7 (PDF 8), §2.3 pp. 8–9 (PDF 9–10)

import Mathlib
import Definitions.Def_TreeOrient_RecGreedy_Model

namespace TreeOrient.RecGreedy

/-- Theorem 1.1, p. 1 (PDF 2), for the specified grouped recursive greedy algorithm. -/
theorem theorem_1_1 : ∀ ε : ℝ, 0 < ε → ∀ a : ℕ, ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (I : Inst n) (k : ℕ),
      IsMonotone I.f →
      NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ)) →
      (∀ S, I.f S ≤ n ^ a) → 3 ≤ k → k ≤ n →
      (∃ T, (stoAlg I a ε k).1 = some T ∧ Feasible I.c I.root ∅ I.B T ∧
        (∃ A : Edges n, A ⊆ T ∧ IsArbo I.root A ∧
          verts I.root A = verts I.root T) ∧
        ∀ A : Edges n, IsArbo I.root A → cost I.c A ≤ I.B → A.card + 1 ≤ k →
          (I.f (verts I.root A) : ℝ) ≤
            C * (Real.log k / Real.log (Real.log k)) *
              (I.f (verts I.root T) : ℝ)) ∧
      ((stoAlg I a ε k).2 : ℝ) ≤
        ((n : ℝ) * Real.logb 2 (I.B + 2)) ^ (C * Real.log k ^ (1 + ε)) := by sorry

end TreeOrient.RecGreedy
