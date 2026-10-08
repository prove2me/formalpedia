-- Prove2me | Theorems.Thm_WhitneyMatroid_Duality_associated_orthogonal_isDual
-- name    : WhitneyMatroid.Duality.associated_orthogonal_isDual
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T12:44:49.70354+00:00
-- url     : https://prove2.me/theorems/3a0837aa-b9e4-49f3-bc27-25aa0296ead0
-- title:
--   Theorem 28 — orthogonal subspaces have dual associated matroids
-- statement:
--   Let $H$ be a hyperplane through the origin (a linear subspace) of $n$-dimensional Euclidean space $E_n$, of dimension $r$, and let $H' = H^\perp$ be the orthogonal hyperplane through the origin, of dimension $n-r$. Let $M$ and $M'$ be the matroids associated with $H$ and $H'$: both have elements $e_1,\dots,e_n$, one per coordinate, and a set $S$ of coordinates has rank in $M$ (resp. $M'$) equal to the dimension of the projection of $H$ (resp. $H'$) onto the coordinate subspace of the coordinates in $S$. Then $M$ and $M'$ are duals under the correspondence of equal coordinates: for every set $N$ of coordinates, with $N'$ its complement,
--
--   $$
--   r_{M'}(N') = r_{M'}(\{e_1,\dots,e_n\}) - n_M(N).
--   $$
--
--   Equivalently, the column matroid of a real matrix and the column matroid of a matrix whose rows span the orthogonal complement of its row space are dual matroids. This is the linear-algebra model of Whitney's abstract duality.
--
--   **Formalization Note** $E_n$ is `EuclideanSpace ℝ (Fin n)` with its standard inner product and $H^\perp$ is Mathlib's orthogonal complement `Hᗮ`. "Associated" is the predicate `IsAssociated` (ground set all of `Fin n`, rank of every subset equal to the dimension of the coordinate projection of the subspace). The dimensions $r$ and $n-r$ are not hypotheses: they are consequences of $H' = H^\perp$. The statement covers $H=\{0\}$ and $H=E_n$ and $n=0$. The correspondence is the identity of the coordinate set, as in Whitney's proof.
-- source:
--   Whitney, On the Abstract Properties of Linear Dependence, Amer. J. Math. 57 (1935), p. 526, Theorem 28

import Mathlib
import Definitions.Def_WhitneyMatroid_Duality_IsDual
import Definitions.Def_WhitneyMatroid_Duality_IsAssociated

namespace WhitneyMatroid.Duality

/-- Whitney, Theorem 28 (p. 526): let `H` be a hyperplane through the origin in `Eₙ` and `H′ = Hᗮ`
the orthogonal hyperplane through the origin. If `M` and `M′` are the matroids associated with `H`
and `H′`, then `M` and `M′` are duals, the correspondence being the one between the coordinates
`e₁, …, eₙ` (the identity of `Fin n`). -/
theorem associated_orthogonal_isDual (n : ℕ) (H : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (M M' : Matroid (Fin n)) (hM : IsAssociated M H) (hM' : IsAssociated M' Hᗮ) :
    IsDualVia M M' (Equiv.refl (Fin n)) := by sorry

end WhitneyMatroid.Duality
