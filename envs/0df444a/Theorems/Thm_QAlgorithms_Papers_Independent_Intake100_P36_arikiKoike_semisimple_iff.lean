-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P36_arikiKoike_semisimple_iff
-- name    : QAlgorithms.Papers.Independent.Intake100.P36.arikiKoike_semisimple_iff
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:54:36.912989+00:00
-- url     : https://prove2.me/theorems/ca8c36c9-d11c-4c83-9def-810b574874c5
-- title:
--   The semisimplicity criterion
-- statement:
--   Let R be a commutative integral domain with identity, let r≥1 and n≥0, let q be a unit of R, and let Q=(Q₁,…,Qᵣ) be an indexed parameter tuple, allowing repeated and zero values. Let H be the Ariki–Koike algebra with the cyclotomic and quadratic polynomial relations equal to zero, and put Lₖ=q^(1−k)Tₖ₋₁⋯T₁T₀T₁⋯Tₖ₋₁. Assume additionally that R is a field. Write [k]_q=1+q+⋯+q^{k−1} and define
--
--   $$P_H(q,Q)=\prod_{k=1}^{n}[k]_q\prod_{1\le s<t\le r}\prod_{-n<d<n}(q^dQ_s-Q_t).$$
--
--   Then $$H\text{ is semisimple}\iff P_H(q,Q)\ne0.$$
--
--   Integer powers use the unit q. Empty products give P_H=1 in degree zero.
-- source:
--   The representation theory of the Ariki-Koike and cyclotomic q-Schur algebras, arXiv:math/0204025v1, PDF p. 13, Corollary 3.3

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P36

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P36

open QAlgorithms.Papers.Independent.Renew46.P26 (Adjacent adjacentPerm nextPosition)

open QAlgorithms.Papers.Independent.Support21.P06 (wordPerm IsReducedWord)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Corollary 3.3, PDF p.13: the exact semisimplicity criterion over any field. -/
theorem arikiKoike_semisimple_iff {R : Type*} [Field R] {r n : ℕ}
    (hr : 1 ≤ r) (q : Rˣ) (Q : Fin r → R) :
    IsSemisimpleRing (ArikiKoike q Q n) ↔ semisimplicityPolynomial q Q n ≠ 0 := by sorry

end QAlgorithms.Papers.Independent.Intake100.P36

end
