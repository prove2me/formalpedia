-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P31_firstColumnUpperBound
-- name    : QAlgorithms.Papers.Independent.Dependency50.P31.firstColumnUpperBound
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:39:11.651296+00:00
-- url     : https://prove2.me/theorems/9fe1289b-c11a-44a4-a826-aa56ddeee246
-- title:
--   First-column upper bound
-- statement:
--   Let $\nu$ have $N\ge2$ boxes and first-column length $c_1$, with $d\ge c_1$. Suppose $(c_1,1)$ is removable. Let $t$ be the standard tableau with $N$ in that box and every other entry in column order. For every unit vector $\psi\in\operatorname{Im}P_t=V^\nu\otimes|t\rangle$, its largest last-particle Schmidt amplitude satisfies
--
--   $$
--   \lambda_1(\psi)^2\le\prod_{i=1}^{c_1-1}\left(1-\frac1{h_{(i,1)}}\right).
--   $$
--
--   This is the first-column estimate used in the general bound.
--
--   **Formalization Note** The printed phrase “For any $|v\rangle$” omits normalization. The unit-state convention in (17), normalized optimization in (55), and proof (60) require $\|\psi\|=1$; scaling otherwise falsifies the printed inequality.
-- source:
--   Lower bound on entanglement in subspaces defined by Young diagrams, arXiv:1805.00364v2, PDF p. 16, Lemma 12, equation (56); proof p.17

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P31

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P31

open scoped ComplexConjugate

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

attribute [local instance] Classical.propDecidable

/-- Lemma 12, arXiv:1805.00364v2 PDF pp.16-17, equations (56)-(60).
The printed 'any v' uses the standing unit-state convention of (17) and (55):
without normalization the inequality is false under scaling. -/
theorem firstColumnUpperBound {d n : ℕ} (hn : 2 ≤ n) (nu : Schur.Partition d n)
    (t : Filling n) (ht : IsTableau nu.val t) (horder : ColumnOrderedExceptLast t)
    (hbox : lastBox t (by omega) = (nu.val.colLen 0-1,0))
    (hcorner : Removable nu.val (nu.val.colLen 0-1,0))
    (psi : H d n) (hpsi : psi ∈ tableauSpace d t) (hunit : ‖psi‖ = 1) :
    largestSchmidtSq psi ≤ cornerBound nu.val (nu.val.colLen 0-1,0) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P31

end
