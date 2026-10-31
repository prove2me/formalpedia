-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P36_arikiKoike_center_separating
-- name    : QAlgorithms.Papers.Independent.Intake100.P36.arikiKoike_center_separating
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:55:31.675423+00:00
-- url     : https://prove2.me/theorems/1519ed3a-3ef8-4bb3-95dc-c6e8947830ef
-- title:
--   The center under corrected separating parameters
-- statement:
--   Let R be a commutative integral domain with identity, let r≥1 and n≥0, let q be a unit of R, and let Q=(Q₁,…,Qᵣ) be an indexed parameter tuple, allowing repeated and zero values. Let H be the Ariki–Koike algebra with the cyclotomic and quadratic polynomial relations equal to zero, and put Lₖ=q^(1−k)Tₖ₋₁⋯T₁T₀T₁⋯Tₖ₋₁. Assume that R is a field, P_H(q,Q)≠0 for the polynomial defined in Corollary 3.3, q≠1, and Q_s≠0 for every s. Then
--
--   $$Z(H)=\{p(L_1,\ldots,L_n):p\in R[X_1,\ldots,X_n]^{S_n}\}.$$
--
--   This is the explicitly corrected separating-parameter statement. The printed theorem omits q≠1 and the nonzero-Q conditions; at r=1,n=2,q=1,Q₁=1 over ℂ its asserted equality is false. Independent moderation of the correction remains required.
-- source:
--   The representation theory of the Ariki-Koike and cyclotomic q-Schur algebras, arXiv:math/0204025v1, PDF p. 13, Theorem 3.4

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P36

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P36

open QAlgorithms.Papers.Independent.Renew46.P26 (Adjacent adjacentPerm nextPosition)

open QAlgorithms.Papers.Independent.Support21.P06 (wordPerm IsReducedWord)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Corrected separating-parameter Theorem 3.4, PDF p.13.
Printed: only P_H≠0. Changed: q≠1 and all Q_s≠0, since the p.12 residue-separation
argument fails at q=1 or a zero component parameter; see the discrepancy ledger. -/
theorem arikiKoike_center_separating {R : Type*} [Field R] {r n : ℕ}
    (hr : 1 ≤ r) (q : Rˣ) (Q : Fin r → R)
    (hP : semisimplicityPolynomial q Q n ≠ 0)
    (hq : (q : R) ≠ 1) (hQ : ∀ s, Q s ≠ 0) :
    ∀ z : ArikiKoike q Q n,
      z ∈ Subalgebra.center R (ArikiKoike q Q n) ↔
        ∃ p : MvPolynomial (Fin n) R, p.IsSymmetric ∧ jmEval q Q p = z := by sorry

end QAlgorithms.Papers.Independent.Intake100.P36

end
