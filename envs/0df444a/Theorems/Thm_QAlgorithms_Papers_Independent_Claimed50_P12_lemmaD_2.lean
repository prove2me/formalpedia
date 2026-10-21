-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P12_lemmaD_2
-- name    : QAlgorithms.Papers.Independent.Claimed50.P12.lemmaD_2
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T18:57:35.657987+00:00
-- url     : https://prove2.me/theorems/f2393217-9e01-446c-8901-571139544872
-- title:
--   Separable approximation of a k-extendible state
-- statement:
--   Let $\omega_{AC}$ be a $k$-extendible density operator on nonzero finite-dimensional systems and let $k\ge1$. Let $\mathcal S_{A:C}$ denote the separable density operators. Then
--
--   $$\inf_{\sigma\in\mathcal S_{A:C}}\Delta(\omega_{AC},\sigma)\le\frac{2(\dim C)^2}{k}.$$
--
--   The infimum is over a nonempty bounded family of distances. The extension definition requires every $A,C_i$ marginal, without assuming any unproved approximation property.
-- source:
--   Quantum conditional mutual information and approximate Markov chains, arXiv:1410.0664v3, PDF p. 28, Lemma D.2

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P12

noncomputable section

open Filter MeasureTheory

open scoped Matrix ComplexConjugate ComplexOrder ENNReal

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Claimed50.P12

open QAlgorithms.Papers.Independent.Information100.P32 (Op)

open QAlgorithms.Papers.Independent.Information100.P69 (CP matrixPower permute)

open QAlgorithms.Papers.Independent.Information100.P80 (OperatorLE groupedPower)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- Lemma D.2, Eq.217 (PDF p.28), including the coefficient two. -/
theorem lemmaD_2 {A C : Type*} [Fintype A] [Fintype C] [DecidableEq A] [DecidableEq C]
    [Nonempty A] [Nonempty C] (omega : Op (A × C)) (homega : IsDensityMatrix omega)
    (k : ℕ) (hk : 0 < k) (hext : KExtendible k omega) :
    separableDistance omega ≤ 2 * (Fintype.card C : ℝ)^2 / (k : ℝ) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P12

end
