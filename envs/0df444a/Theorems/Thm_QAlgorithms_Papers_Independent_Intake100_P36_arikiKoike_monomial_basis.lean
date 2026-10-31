-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P36_arikiKoike_monomial_basis
-- name    : QAlgorithms.Papers.Independent.Intake100.P36.arikiKoike_monomial_basis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:53:59.333784+00:00
-- url     : https://prove2.me/theorems/cb358553-1d54-4d6a-9ab5-454e4274f08d
-- title:
--   The explicit Ariki–Koike monomial basis
-- statement:
--   Let R be a commutative integral domain with identity, let r≥1 and n≥0, let q be a unit of R, and let Q=(Q₁,…,Qᵣ) be an indexed parameter tuple, allowing repeated and zero values. Let H be the Ariki–Koike algebra with the cyclotomic and quadratic polynomial relations equal to zero, and put Lₖ=q^(1−k)Tₖ₋₁⋯T₁T₀T₁⋯Tₖ₋₁. For w∈Sₙ, let T_w be the product along a reduced adjacent expression. Then the following family is an R-basis of H:
--
--   $$\{L_1^{a_1}\cdots L_n^{a_n}T_w:0\le a_i<r,\ w\in S_n\}.$$
--
--   This gives both linear independence and spanning without a rank or freeness hypothesis. In degree zero the single basis element is the empty product 1.
-- source:
--   The representation theory of the Ariki-Koike and cyclotomic q-Schur algebras, arXiv:math/0204025v1, PDF p. 4, Theorem 2.2

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P36

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P36

open QAlgorithms.Papers.Independent.Renew46.P26 (Adjacent adjacentPerm nextPosition)

open QAlgorithms.Papers.Independent.Support21.P06 (wordPerm IsReducedWord)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 2.2, PDF p.4: the displayed monomials form an R-basis.
Neither freeness nor the rank is assumed. Both printed polynomial RHSs are corrected to zero. -/
theorem arikiKoike_monomial_basis {R : Type*} [CommRing R] [IsDomain R]
    {r n : ℕ} (hr : 1 ≤ r) (q : Rˣ) (Q : Fin r → R) :
    LinearIndependent R (arikiKoikeMonomial (n := n) q Q) ∧
      Submodule.span R (Set.range (arikiKoikeMonomial (n := n) q Q)) = ⊤ := by sorry

end QAlgorithms.Papers.Independent.Intake100.P36

end
