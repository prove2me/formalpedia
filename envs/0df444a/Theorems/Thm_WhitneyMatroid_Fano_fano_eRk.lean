-- Prove2me | Theorems.Thm_WhitneyMatroid_Fano_fano_eRk
-- name    : WhitneyMatroid.Fano.fano_eRk
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T04:49:53.539094+00:00
-- url     : https://prove2.me/theorems/a8d9a058-9140-4ed4-a959-1d055c95d466
-- title:
--   §16 — the rank function of the matroid $M'$
-- statement:
--   Let $M$ be the matroid $M'$ of §16: elements $1,\dots,7$, bases all three-element sets except $124,135,167,236,257,347,456$ (16.1). For every set $S$ of $k$ elements,
--
--   $$
--   r(S)=\begin{cases} k & k\le 2,\\ 3 & k\ge 4,\\ 2 & k=3,\ S\in(16.1),\\ 3 & k=3,\ S\notin(16.1).\end{cases}
--   $$
--
--   This is the explicit rank function of the Fano matroid; it is what one checks against the ranks of submatrices when testing whether a matrix corresponds to $M'$.
--
--   **Formalization Note** The elements are `Fin 7` (Whitney's $k$ is `k - 1`); the size of $S$ is `Set.ncard`, and ranks are `M.eRk`.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 529, §16

import Mathlib
import Definitions.Def_WhitneyMatroid_Fano_IsFano

namespace WhitneyMatroid.Fano

/-- Whitney §16 (p. 529): in the matroid `M′` of §16 (rank defined in terms of bases), each set of
`k` elements has rank `k` if `k ≤ 2` and rank `3` if `k ≥ 4`; a set of three elements has rank `2`
if it is one of the sets (16.1) and rank `3` otherwise. -/
theorem fano_eRk (M : Matroid (Fin 7)) (hM : IsFano M) (S : Set (Fin 7)) :
    (S.ncard ≤ 2 → M.eRk S = S.ncard) ∧
      (4 ≤ S.ncard → M.eRk S = 3) ∧
      (S.ncard = 3 → S ∈ fanoLines → M.eRk S = 2) ∧
      (S.ncard = 3 → S ∉ fanoLines → M.eRk S = 3) := by sorry

end WhitneyMatroid.Fano
