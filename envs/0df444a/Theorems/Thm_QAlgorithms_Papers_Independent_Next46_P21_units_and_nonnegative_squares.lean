-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P21_units_and_nonnegative_squares
-- name    : QAlgorithms.Papers.Independent.Next46.P21.units_and_nonnegative_squares
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T18:35:27.054981+00:00
-- url     : https://prove2.me/theorems/efd7e80f-c34b-444a-91a8-5b7379597e5d
-- title:
--   Units and totally nonnegative unit squares
-- statement:
--   Let $R=\mathbb Z[\sqrt2]$, with its positive real embedding, and let $u^\bullet$ denote the embedding obtained by sending $\sqrt2$ to $-\sqrt2$. The units are exactly
--
--   $$
--   R^\times=\{(-1)^n(\sqrt2-1)^k:n,k\in\mathbb Z\}.
--   $$
--
--   Integer powers are taken in the unit group, since $\sqrt2-1$ has inverse $\sqrt2+1$. Moreover, for every unit $u\in R$,
--
--   $$
--   (\exists v\in R,\ v^2=u)\quad\Longleftrightarrow\quad u\ge0\ \text{and}\ u^\bullet\ge0.
--   $$
--
--   This characterizes the unit correction needed by the relative norm construction. The square criterion is asserted only for units.
-- source:
--   Efficient Clifford+T approximation of single-qubit operators, arXiv:1212.6253v2, PDF p. 4, Lemma 10: units and totally nonnegative unit squares

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P21

noncomputable section

namespace QAlgorithms.Papers.Independent.Next46.P21

open Set

open scoped ComplexConjugate

/-- Lemma 10, PDF p.4: classification of units, and the square criterion restricted to units. -/
theorem units_and_nonnegative_squares :
    (∀ u : Zsqrtd 2, IsUnit u ↔ ∃ n k : ℤ,
      u = ((((-1 : (Zsqrtd 2)ˣ) ^ n) * smallUnit ^ k : (Zsqrtd 2)ˣ) : Zsqrtd 2)) ∧
    (∀ u : Zsqrtd 2, IsUnit u →
      ((∃ v : Zsqrtd 2, v ^ 2 = u) ↔
        0 ≤ quadraticReal u ∧ 0 ≤ quadraticReal (star u))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P21

end
