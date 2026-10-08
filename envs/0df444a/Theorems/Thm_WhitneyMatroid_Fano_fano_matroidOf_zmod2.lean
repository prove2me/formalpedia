-- Prove2me | Theorems.Thm_WhitneyMatroid_Fano_fano_matroidOf_zmod2
-- name    : WhitneyMatroid.Fano.fano_matroidOf_zmod2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:50:04.316983+00:00
-- url     : https://prove2.me/theorems/bdb3ebd2-054c-46f5-ae7d-13a6dfd9e5d1
-- title:
--   p. 533 — the matroid $M'$ is the matroid of a matrix of integers mod 2
-- statement:
--   The matroid $M'$ of §16 (seven elements, bases all three-element sets except $124,135,167,236,257,347,456$) exists and is the matroid of the $3\times 7$ matrix of integers mod 2
--
--   $$
--   \begin{pmatrix}
--   1&0&0&1&1&0&1\\
--   0&1&0&1&0&1&1\\
--   0&0&1&0&1&1&1
--   \end{pmatrix},
--   $$
--
--   obtained from Whitney's normal form (16.3) with $a=b=c=d=1$ by transposing the left-hand portion, dropping the last row and column of the right-hand portion, and interchanging the two parts. The relation $2a=0$ that rules out real matrices in §16 holds mod 2, so the field in the goal theorem matters.
--
--   **Formalization Note** Ranks of submatrices are computed over the field `ZMod 2`; Whitney's element $k$ is the column `k - 1`.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 533

import Mathlib
import Definitions.Def_WhitneyMatroid_Fano_IsMatroidOf
import Definitions.Def_WhitneyMatroid_Fano_IsFano

namespace WhitneyMatroid.Fano

/-- Whitney, p. 533: the matroid `M′` of §16 corresponds to a matrix of integers mod 2, namely the
`3 × 7` matrix built from (16.3) with `a = b = c = d = 1` (columns `1, 2, 3` the unit vectors,
columns `4, 5, 6, 7` equal to `(1,1,0), (1,0,1), (0,1,1), (1,1,1)`). -/
theorem fano_matroidOf_zmod2 :
    ∃ M : Matroid (Fin 7), IsFano M ∧
      IsMatroidOf M (!![1, 0, 0, 1, 1, 0, 1;
                        0, 1, 0, 1, 0, 1, 1;
                        0, 0, 1, 0, 1, 1, 1] : Matrix (Fin 3) (Fin 7) (ZMod 2)) := by sorry

end WhitneyMatroid.Fano
