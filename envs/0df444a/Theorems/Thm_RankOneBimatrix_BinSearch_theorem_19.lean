-- Prove2me | Theorems.Thm_RankOneBimatrix_BinSearch_theorem_19
-- name    : RankOneBimatrix.BinSearch.theorem_19
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:35:08.655502+00:00
-- url     : https://prove2.me/theorems/41d643e3-8d9c-405b-a7ca-9dde5a7c5384
-- title:
--   Theorem 19, p. 21 — BINSEARCH finds an equilibrium in polynomial time
-- statement:
--   For every nonempty rational input $(A,a,b)$ and every admissible extreme-optimal LP oracle, BINSEARCH halts at its first successful test after polynomially many main-loop iterations in the combined bit length $L$. All actual LP calls are genuine, every midpoint and returned parameter has polynomial bit length, and the final primal strategy paired with any optimal final dual strategy is a Nash equilibrium of $(A,-A+ab^\top)$.
--
--   $$\exists p\in\mathbb N[T]\ \forall A,a,b,O\ \exists k\le p(L):\quad x_k^{*\top}a=\lambda_k^*,\quad (x_k^*,y^*)\in\operatorname{NE}(A,-A+ab^\top).$$
--
--   This is the paper's main algorithmic result. **Formalization Note** Polynomial time is represented by the iteration bound and the midpoint and returned-parameter bit-size bounds under the assumed polynomial-time LP solvers; no machine model is asserted. The implicit conditions $m,n>0$ are explicit.
-- source:
--   Adsul, Garg, Mehta, Sohoni, von Stengel, Fast Algorithms for Rank-1 Bimatrix Games, arXiv:1812.04611v4, p. 21, Theorem 19; pp. 20–22, Figure 2 and proof

import Definitions.Def_RankOneBimatrix_BinSearch_Algorithm

namespace RankOneBimatrix.BinSearch
open Matrix

/-- Theorem 19, p. 21: Figure 2 finds an equilibrium in polynomial time. -/
theorem theorem_19 :
    ∃ p : Polynomial ℕ,
      ∀ (m n : ℕ), 0 < m → 0 < n →
      ∀ (A : Matrix (Fin m) (Fin n) ℚ) (a : Fin m → ℚ) (b : Fin n → ℚ)
        (O : Oracle m n),
        Admissible (A.map (fun r => (r : ℝ)))
          (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O →
        ∃ k : ℕ,
          k ≤ p.eval (inputSize A a b) ∧
          stop (A.map (fun r => (r : ℝ))) (fun i => (a i : ℝ))
            (fun j => (b j : ℝ)) O k ∧
          (∀ j < k, ¬ stop (A.map (fun r => (r : ℝ)))
            (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O j) ∧
          (∀ j ≤ k, callsGenuine (A.map (fun r => (r : ℝ)))
            (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O j) ∧
          (∀ j ≤ k, ∃ q : ℚ,
            (q : ℝ) = midpoint (A.map (fun r => (r : ℝ)))
              (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O j ∧
            ratSize q ≤ p.eval (inputSize A a b)) ∧
          (∀ j ≤ k, ∃ q : ℚ,
            (q : ℝ) = lamStar (A.map (fun r => (r : ℝ)))
              (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O j ∧
            ratSize q ≤ p.eval (inputSize A a b)) ∧
          O.dual (lamStar (A.map (fun r => (r : ℝ)))
            (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O k) ∈
            DExtreme (A.map (fun r => (r : ℝ))) (fun j => (b j : ℝ))
              (lamStar (A.map (fun r => (r : ℝ)))
                (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O k) ∧
          (∀ y t, (y, t) ∈ Yopt (A.map (fun r => (r : ℝ)))
              (fun j => (b j : ℝ))
              (lamStar (A.map (fun r => (r : ℝ)))
                (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O k) →
            IsNE (A.map (fun r => (r : ℝ)))
              (rankOneB (A.map (fun r => (r : ℝ)))
                (fun i => (a i : ℝ)) (fun j => (b j : ℝ)))
              (xStar (A.map (fun r => (r : ℝ)))
                (fun i => (a i : ℝ)) (fun j => (b j : ℝ)) O k) y) := by sorry

end RankOneBimatrix.BinSearch
