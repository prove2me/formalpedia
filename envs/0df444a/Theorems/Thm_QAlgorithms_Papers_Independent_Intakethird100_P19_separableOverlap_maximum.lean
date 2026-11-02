-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P19_separableOverlap_maximum
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P19.separableOverlap_maximum
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T07:34:11.863796+00:00
-- url     : https://prove2.me/theorems/2ff15be5-f2fd-4d37-b178-35cd6ddafa8e
-- title:
--   Lemma 6: attained maximum separable overlap
-- statement:
--   All Hilbert spaces are finite-dimensional complex spaces with fixed product bases and positive local dimensions. States are positive semidefinite operators of trace one; pure kets have norm one. Let $\psi$ be bipartite pure, with largest squared Schmidt coefficient $\lambda_1$. Let $\mathcal S$ be the separable density matrices on the same register. Then
--
--   $$\operatorname{Tr}(\psi\sigma)\le\lambda_1\quad(\sigma\in\mathcal S),\qquad \exists\sigma_*\in\mathcal S:\operatorname{Tr}(\psi\sigma_*)=\lambda_1.$$
--
--   This records the maximum with attainment, not only a supremum bound.
-- source:
--   Entanglement manipulation and distillability beyond LOCC, arXiv:1711.03835v2, PDF p. 10, Lemma 6

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P19

noncomputable section

open QAlgorithms QAlgorithms.Entanglement Filter

open scoped Matrix ComplexOrder ComplexConjugate ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Intakethird100.P19

open QAlgorithms.Papers.Independent.Information100.P21 (Op FiniteLOCC)

open QAlgorithms.Papers.Independent.Information100.P19 (Bip)

open QAlgorithms.Papers.Independent.Information100.P69 (CP)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower SupportIncluded)

open QAlgorithms.Papers.Independent.Dependency50.P19 (epr)

/-- Lemma 6, PDF pp.10-11, credited to Shimony [28]: the maximum
separable overlap is the largest squared Schmidt coefficient, and is attained. -/
theorem separableOverlap_maximum {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (psi : UnitBipartiteKet a b) :
    (∀ sigma : Bip a b, SeparableState sigma →
      (psi.rho * sigma).trace.re ≤ schmidtAt psi.ket 0) ∧
    ∃ sigma : Bip a b, SeparableState sigma ∧
      (psi.rho * sigma).trace.re = schmidtAt psi.ket 0 := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P19

end
