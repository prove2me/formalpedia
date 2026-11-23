-- Prove2me | Theorems.Thm_RamseyValues_ramsey_recursion
-- name    : RamseyValues.ramsey_recursion
-- status  : Open
-- author  : @LG
-- created : 2026-11-22T23:56:55.919529+00:00
-- url     : https://prove2.me/theorems/861771ca-6368-4115-9343-3da90fb8309f
-- title:
--   Erdős–Szekeres recursion $R(k,\ell)\le R(k-1,\ell)+R(k,\ell-1)$
-- statement:
--   The Erdős–Szekeres recursion: for integers $k,\ell\ge 2$,
--   $$R(k,\ell)\le R(k-1,\ell)+R(k,\ell-1).$$
--   Together with the boundary values $R(1,\ell)=R(k,1)=1$ it yields $R(k,\ell)\le\binom{k+\ell-2}{k-1}$ by induction, and it is the engine behind the classical small-value upper bounds. A proof splits the neighbours and non-neighbours of a fixed vertex and applies the pigeonhole principle.
--
--   **Formalization Note.** Stated for `Erdos77.asymmetricRamsey` with hypotheses `2 ≤ k` and `2 ≤ l`, so the natural-number subtractions `k-1` and `l-1` are genuine predecessors.
-- source:
--   P. Erdős and G. Szekeres, A combinatorial problem in geometry, Compositio Math. 2 (1935) 463–470, http://www.numdam.org/item/CM_1935__2__463_0/ (the recursion underlying the bound R(k,l) ≤ C(k+l−2,k−1)).

import Mathlib
import Definitions.Def_Erdos77_asymmetric_ramsey

namespace RamseyValues

theorem ramsey_recursion (k l : ℕ) (hk : 2 ≤ k) (hl : 2 ≤ l) :
    Erdos77.asymmetricRamsey k l ≤ Erdos77.asymmetricRamsey (k - 1) l + Erdos77.asymmetricRamsey k (l - 1) := by sorry

end RamseyValues
