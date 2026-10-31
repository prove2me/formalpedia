-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P36_murphy_jm_triangular
-- name    : QAlgorithms.Papers.Independent.Intake100.P36.murphy_jm_triangular
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:57:18.938667+00:00
-- url     : https://prove2.me/theorems/89770215-88d6-4550-bdd2-36c204fe7637
-- title:
--   Triangular JM action on the Murphy basis
-- statement:
--   Let R be a commutative integral domain with identity, let r≥1 and n≥0, let q be a unit of R, and let Q=(Q₁,…,Qᵣ) be an indexed parameter tuple, allowing repeated and zero values. Let H be the Ariki–Koike algebra with the cyclotomic and quadratic polynomial relations equal to zero, and put Lₖ=q^(1−k)Tₖ₋₁⋯T₁T₀T₁⋯Tₖ₋₁. Use the multipartitions, tableaux, elements m_{st}, and higher-shape span H^λ of Theorem 3.8. Tableau dominance compares the shapes of every initial subtableau. Fix λ⊢n, t∈Std(λ), and 1≤k≤n. If k lies at row i, column j, component c of t, put res_t(k)=q^{j−i}Q_c. There are coefficients c_v∈R, independent of the row tableau s, such that
--
--   $$m_{st}L_k-\operatorname{res}_t(k)m_{st}-\sum_{v\triangleright t}c_vm_{sv}\in H^\lambda\qquad(s\in\operatorname{Std}(\lambda)).$$
--
--   This statement uses the actual JM elements and requires no semisimplicity, separation, or nonzero component parameters.
-- source:
--   The representation theory of the Ariki-Koike and cyclotomic q-Schur algebras, arXiv:math/0204025v1, PDF p. 19, Proposition 3.14

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P36

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P36

open QAlgorithms.Papers.Independent.Renew46.P26 (Adjacent adjacentPerm nextPosition)

open QAlgorithms.Papers.Independent.Support21.P06 (wordPerm IsReducedWord)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Proposition 3.14, PDF p.19: triangular JM action, uniform in the row tableau.
The shape is the common tableau shape. This holds without any separation assumption. -/
theorem murphy_jm_triangular {R : Type*} [CommRing R] [IsDomain R]
    {r n : ℕ} (hr : 1 ≤ r) (q : Rˣ) (Q : Fin r → R)
    (lam : MultiPartition r n) (t : StandardMultiTableau lam) (k : Fin n) :
    ∃ coeff : StandardMultiTableau lam → R, ∀ s : StandardMultiTableau lam,
      murphy q Q s t * cyclotomicJM q Q k - tableauResidue q Q t k • murphy q Q s t -
        ∑ v ∈ Finset.univ.filter (fun v : StandardMultiTableau lam => TableauDominates v t ∧ v ≠ t),
          coeff v • murphy q Q s v ∈ higherMurphySpan q Q lam := by sorry

end QAlgorithms.Papers.Independent.Intake100.P36

end
