-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Renew46_P26_remark_5_6
-- name    : QAlgorithms.Papers.Independent.Renew46.P26.remark_5_6
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-20T21:02:40.196827+00:00
-- url     : https://prove2.me/theorems/20df900f-642c-4bc1-9e4a-68b6debeba31
-- title:
--   Remark 5.6
-- statement:
--   For same-shape standard tableaux $T,U$, let $s$ send the label in each box of $T$ to the label in that box of $U$, and let $\ell(s)$ be its inversion number. There is an admissible tableau chain from $T$ to $U$ of length $\ell(s)$, and
--
--   $$\ell(s)\leq m$$
--
--   for every expression of this relabelling by $m$ adjacent transpositions, even when intermediate fillings need not be tableaux. This states geodesicity on each fixed-shape orbit; no path is asserted between arbitrary different shapes.
-- source:
--   A New Approach to the Representation Thoery of the Symmetric Groups. 2, arXiv:math/0503040v3, PDF p. 21, Remark 5.6

import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P26

noncomputable section

namespace QAlgorithms.Papers.Independent.Renew46.P26

open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-- Remark 5.6 (PDF p.21). Equal-shape tableaux admit an admissible path of
inversion length. The lower bound ranges over all adjacent-swapAlgebraElement words,
including words whose intermediate fillings fail to be tableaux. Different-shape
vectors need not share an orbit. -/
theorem remark_5_6 {n : ℕ} (T U : YoungTableau n) (h : tableauShape T = tableauShape U) :
    (∃ r : ℕ, ∃ chain : Fin (r + 1) → YoungTableau n,
      chain 0 = T ∧ chain (Fin.last r) = U ∧
      (∀ j : Fin r, TableauStep (chain j.castSucc) (chain j.succ)) ∧
      r = inversionsBetween T U) ∧
    (∀ word : List (Adjacent n),
      U.val = T.val ∘ (word.map adjacentPerm).prod →
      inversionsBetween T U ≤ word.length) := by sorry

end QAlgorithms.Papers.Independent.Renew46.P26

end
