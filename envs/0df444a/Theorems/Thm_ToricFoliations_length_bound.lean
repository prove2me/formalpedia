-- Prove2me | Theorems.Thm_ToricFoliations_length_bound
-- name    : ToricFoliations.length_bound
-- status  : Open
-- author  : @hiraeth
-- created : 2026-10-07T12:32:39.905423+00:00
-- url     : https://prove2.me/theorems/f17af3ac-ba42-4163-81e3-0cc90690d016
-- title:
--   Theorem 1.3(1) — the length bound $l_{\mathscr F}(R)\le r+1$
-- statement:
--   **theorem_title:** Theorem 1.3(1) — the length bound $l_{\mathscr F}(R)\le r+1$
--
--   Let $X$ be a projective $\mathbb Q$-factorial toric variety and let
--   $\mathscr F$ be a toric foliation of rank $r$ on $X$, represented by the
--   subspace $V\subseteq N_{\mathbb C}$. For every extremal ray $R$ of the Mori
--   cone $\overline{\mathrm{NE}}(X)$, the length of $R$ with respect to the
--   foliation satisfies
--
--   $$
--   l_{\mathscr F}(R)=\min_{[C]\in R}\{-K_{\mathscr F}\cdot C\}\le r+1.
--   $$
--
--   **Formalization Note.** `rayLength R V` implements the minimum; `R` is an
--   `ExtremalRay n` with the (opaque) `isExtremal` predicate whose concretization
--   is future work.
-- source:
--   Fujino--Sato 2024, A remark on toric foliations, Arch. Math. 122 (2024) 621--627, https://doi.org/10.1007/s00013-024-01991-1 (arXiv:2309.09461), Section 1, Theorem 1.3(1)

import Mathlib
import Definitions.Def_ToricFoliations

open scoped BigOperators

namespace ToricFoliations

/--
Theorem 1.3(1) of the paper: for every extremal ray `R` of the Mori cone,
the length of `R` with respect to a toric foliation of rank `r` satisfies

`l_F(R) <= r + 1`.
-/
theorem length_bound {n r : ℕ} (R : ExtremalRay n) (hExt : R.isExtremal)
    (V : Submodule ℂ (Complexified n))
    (hrank : Module.finrank ℂ V = r) :
    rayLength R V ≤ r + 1 := by
  sorry

end ToricFoliations
