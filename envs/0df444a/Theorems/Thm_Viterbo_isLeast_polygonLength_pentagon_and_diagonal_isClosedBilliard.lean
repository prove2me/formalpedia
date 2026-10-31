-- Prove2me | Theorems.Thm_Viterbo_isLeast_polygonLength_pentagon_and_diagonal_isClosedBilliard
-- name    : Viterbo.isLeast_polygonLength_pentagon_and_diagonal_isClosedBilliard
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T08:13:51.348465+00:00
-- url     : https://prove2.me/theorems/d5529c27-fdf3-4919-b9a4-d82745a0615c
-- title:
--   Proof of Proposition 1.4 — the diagonals are 2-bounce billiards of T°-length 2cos(π/10)(1 + cos(π/5)), the least over P(K) with at most 3 vertices
-- statement:
--   For the regular pentagon $K \subset \mathbb R^2$ with vertices $v_k = (\cos\frac{2\pi k}{5}, \sin\frac{2\pi k}{5})$ and its rotation $T$:
--   - the least $T^\circ$-length $\sum_i h_T(q_{i+1} - q_i)$ of a closed polygonal curve with at most $3$ vertices that cannot be translated into the interior of $K$ is $2\cos(\frac{\pi}{10})(1 + \cos(\frac{\pi}{5}))$: some such curve has this length, and none is shorter;
--   - for each $k$, the 2-bounce curve $(v_k, v_{k+2})$ along a diagonal of $K$ is a closed $T$-billiard trajectory in $K$ (Definition 2.1), of $T^\circ$-length $2\cos(\frac{\pi}{10})(1 + \cos(\frac{\pi}{5}))$.
-- source:
--   Haim-Kislev, P. and Ostrover, Y., A counterexample to Viterbo's conjecture, Ann. of Math. (2) 203 (2026) 603–622, https://doi.org/10.4007/annals.2026.203.2.5 (arXiv:2405.16513v3, whose page numbers are used), pp. 11–12, the minimization in the proof of Proposition 1.4

import Mathlib
import Definitions.Def_SymmetricPolar
import Definitions.Def_Viterbo

namespace Viterbo

theorem isLeast_polygonLength_pentagon_and_diagonal_isClosedBilliard :
    IsLeast {L : ℝ | ∃ (m : ℕ) (q : Fin m → OAI.SymmetricPolar.Position 2), m ≤ 3 ∧
        NotTranslatableIntoInterior pentagonK q ∧ L = polygonLength pentagonT q}
      (2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5))) ∧
    ∀ k : ℕ, k < 5 →
      IsClosedBilliard pentagonK pentagonT ![pentagonVertex k, pentagonVertex (k + 2)] ∧
      polygonLength pentagonT ![pentagonVertex k, pentagonVertex (k + 2)] =
        2 * Real.cos (Real.pi / 10) * (1 + Real.cos (Real.pi / 5)) := by
  sorry

end Viterbo
