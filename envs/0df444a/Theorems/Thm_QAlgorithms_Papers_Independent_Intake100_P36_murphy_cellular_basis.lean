-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intake100_P36_murphy_cellular_basis
-- name    : QAlgorithms.Papers.Independent.Intake100.P36.murphy_cellular_basis
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-30T11:56:42.78027+00:00
-- url     : https://prove2.me/theorems/b589b323-4b0d-4396-a73e-2929d2a4ec0a
-- title:
--   The computed Murphy family is a cellular basis
-- statement:
--   Let R be a commutative integral domain with identity, let r≥1 and n≥0, let q be a unit of R, and let Q=(Q₁,…,Qᵣ) be an indexed parameter tuple, allowing repeated and zero values. Let H be the Ariki–Koike algebra with the cyclotomic and quadratic polynomial relations equal to zero, and put Lₖ=q^(1−k)Tₖ₋₁⋯T₁T₀T₁⋯Tₖ₋₁. For each r-multipartition λ of n, let t^λ be its row reading tableau, S_λ its row stabilizer, and d(t) the permutation with t=t^λd(t). Define x_λ=∑_{w∈S_λ}T_w, u_λ^+=∏_{s=2}^r∏_{k=1}^{|λ⁽¹⁾|+⋯+|λ⁽ˢ⁻¹⁾|}(L_k−Q_s), m_λ=x_λu_λ^+, and m_{st}=T_{d(s)^{-1}}m_λT_{d(t)} for standard tableaux s,t of the same shape. Then
--
--   $$\{m_{st}:\lambda\vdash n,\ s,t\in\operatorname{Std}(\lambda)\}$$
--
--   is an R-basis of H. There is an involutory R-linear algebra anti-automorphism * fixing every T_i and satisfying m_{st}*=m_{ts}. If H^λ is the R-span of basis elements of shapes strictly dominating λ, then for every standard t of shape λ and every h∈H there are coefficients c_v∈R, independent of s, such that
--
--   $$m_{st}h-\sum_{v\in\operatorname{Std}(\lambda)}c_vm_{sv}\in H^\lambda\qquad(s\in\operatorname{Std}(\lambda)).$$
--
--   Both cellular axioms concern these explicitly computed elements of the presented algebra.
-- source:
--   The representation theory of the Ariki-Koike and cyclotomic q-Schur algebras, arXiv:math/0204025v1, PDF p. 16, Theorem 3.8

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P36

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Intake100.P36

open QAlgorithms.Papers.Independent.Renew46.P26 (Adjacent adjacentPerm nextPosition)

open QAlgorithms.Papers.Independent.Support21.P06 (wordPerm IsReducedWord)

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 3.8 and both cellular axioms, PDF pp.16-17.
The anti-involution is required to fix T_i, and the multiplication coefficients are
chosen before the row tableau s. No cellularity or basis hypothesis is present. -/
theorem murphy_cellular_basis {R : Type*} [CommRing R] [IsDomain R]
    {r n : ℕ} (hr : 1 ≤ r) (q : Rˣ) (Q : Fin r → R) :
    LinearIndependent R (murphyFamily (n := n) q Q) ∧
      Submodule.span R (Set.range (murphyFamily (n := n) q Q)) = ⊤ ∧
      ∃ star : ArikiKoike q Q n →ₗ[R] ArikiKoike q Q n,
        Function.Involutive star ∧
        (∀ x y, star (x * y) = star y * star x) ∧
        (∀ i, i < n → star (akT q Q n i) = akT q Q n i) ∧
        (∀ (lam : MultiPartition r n) (s t : StandardMultiTableau lam),
          star (murphy q Q s t) = murphy q Q t s) ∧
        (∀ (lam : MultiPartition r n) (t : StandardMultiTableau lam) (h : ArikiKoike q Q n),
          ∃ coeff : StandardMultiTableau lam → R, ∀ s : StandardMultiTableau lam,
            murphy q Q s t * h - ∑ v : StandardMultiTableau lam, coeff v • murphy q Q s v ∈
              higherMurphySpan q Q lam) := by sorry

end QAlgorithms.Papers.Independent.Intake100.P36

end
