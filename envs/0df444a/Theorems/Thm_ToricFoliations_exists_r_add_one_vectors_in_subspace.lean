-- Prove2me | Theorems.Thm_ToricFoliations_exists_r_add_one_vectors_in_subspace
-- name    : ToricFoliations.exists_r_add_one_vectors_in_subspace
-- status  : Open
-- author  : @hiraeth
-- created : 2026-10-07T12:31:37.741993+00:00
-- url     : https://prove2.me/theorems/a79da369-52ce-46aa-9ca2-9ddee98f4229
-- title:
--   A long ray forces at least $r+1$ wall vectors in $V$
-- statement:
--   **theorem_title:** A long ray forces at least $r+1$ wall vectors in $V$
--
--   Let $\mathscr F$ be a toric foliation of rank $r$ on a projective
--   $\mathbb Q$-factorial toric variety, represented by the subspace
--   $V\subseteq N_{\mathbb C}$. Let $C=V(W)$ be a torus-invariant curve with wall
--   data as in equation (3.1) normalized by the ordering (3.2). If the foliated
--   length satisfies
--
--   $$
--   -K_{\mathscr F}\cdot C > r,
--   $$
--
--   then at least $r+1$ of the vectors $v_1,\dots,v_{n+1}$ belong to $V$:
--
--   $$
--   \exists\, i_1<\cdots<i_{r+1}\ \text{such that}\
--   v_{i_1},\dots,v_{i_{r+1}}\in V.
--   $$
--
--   This is equation (3.3) of the paper; it follows from $D_{v_i}\cdot C\le1$ for
--   all $i$ and from $\dim_{\mathbb C}V=r$.
--
--   **Formalization Note.** The conclusion is an injective map
--   `ι : Fin (r+1) → Fin (n+1)` with `toComplex (C.v (ι j)) ∈ V` for all `j`.
-- source:
--   Fujino--Sato 2024, A remark on toric foliations, Arch. Math. 122 (2024) 621--627, https://doi.org/10.1007/s00013-024-01991-1 (arXiv:2309.09461), Section 3, eq. (3.3)

import Mathlib
import Definitions.Def_ToricFoliations

open scoped BigOperators

namespace ToricFoliations

/--
If `-K_F . C > r` and `rank F = r`, then at least `r+1` of the vectors
`v_1,...,v_{n+1}` lie in `V`.  This is the pigeonhole
step (3.3) of the proof of Theorem 1.3, using `D . C <= 1`.
-/
theorem exists_r_add_one_vectors_in_subspace {n r : ℕ} (C : WallData n)
    (V : Submodule ℂ (Complexified n))
    (hrank : Module.finrank ℂ V = r)
    (hlong : r < curveLength C V) :
    ∃ ι : Fin (r + 1) → Fin (n + 1),
      Function.Injective ι ∧
        ∀ j : Fin (r + 1), toComplex (C.v (ι j)) ∈ V := by
  sorry

end ToricFoliations
