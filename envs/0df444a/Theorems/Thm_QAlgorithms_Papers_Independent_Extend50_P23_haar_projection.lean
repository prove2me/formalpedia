-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P23_haar_projection
-- name    : QAlgorithms.Papers.Independent.Extend50.P23.haar_projection
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T17:40:39.044998+00:00
-- url     : https://prove2.me/theorems/be992a5a-95a5-488b-9e33-69a7901b9d8f
-- title:
--   Normalized Haar averaging projects onto the full commutant
-- statement:
--   Let $G$ be a compact Hausdorff topological group, $\mu$ its regular Borel Haar probability measure, and $\rho:G\to U(n)$ a continuous representation, where $n\ge0$. For an arbitrary complex matrix $X$, put $\mathcal C_\rho=\{Y:\rho(g)Y=Y\rho(g)\text{ for every }g\}$ and define
--
--   $$
--   P_\rho(X)=\int_G\rho(g)X\rho(g)^\dagger\,d\mu(g).
--   $$
--
--   The integrand is Bochner integrable, $P_\rho(X)\in\mathcal C_\rho$, and $P_\rho(X)=X$ whenever $X\in\mathcal C_\rho$. Furthermore, $\langle Y,X-P_\rho(X)\rangle_{\rm HS}=0$ for every $Y\in\mathcal C_\rho$, where $\langle A,B\rangle_{\rm HS}=\sum_{a,b}\overline{A_{ab}}B_{ab}$. For finite $G$ this is exactly
--
--   $$
--   P_\rho(X)=\frac1{|G|}\sum_{g\in G}\rho(g)X\rho(g)^\dagger.
--   $$
--
--   Thus the operation is the orthogonal projection onto the full commutant, including non-Hermitian matrices. This exact primitive does not assert correctness of a numerical approximation.
-- source:
--   RepLAB: a computational/numerical approach to representation theory, arXiv:1911.09154v1, PDF p. 4, §2.1, Eq.(8)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Extend50.P23

open MeasureTheory

open scoped ComplexConjugate BigOperators Matrix.Norms.Elementwise

open QAlgorithms.Papers.Independent.Support21.P09 (EquivalentModels)

open QAlgorithms.Papers.Independent.Dependency50.P05 (UnitaryBetween)

/-- PDF p.4, Eq.(8): the normalized Haar average is the Hilbert–Schmidt
projection onto the full commutant, including its finite-group formula.
No Hermitian, positivity, or trace-one restriction is placed on X. -/
theorem haar_projection {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G]
    (mu : Measure G) [Measure.IsHaarMeasure mu] [Measure.Regular mu]
    [IsProbabilityMeasure mu] {n : ℕ}
    (rho : G → Matrix (Fin n) (Fin n) ℂ) (hrho : IsUnitaryRepresentation rho)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    (∀ a b : Fin n, Integrable (fun g => (rho g * X * (rho g).conjTranspose) a b) mu) ∧
    Commutes rho (representationHaarProjection rho mu X) ∧
    (Commutes rho X → representationHaarProjection rho mu X = X) ∧
    (∀ Y : Matrix (Fin n) (Fin n) ℂ, Commutes rho Y →
      (∑ a, ∑ b, conj (Y a b) * (X - representationHaarProjection rho mu X) a b) = 0) ∧
    (∀ s : Finset G, (∀ g, g ∈ s) →
      representationHaarProjection rho mu X = (s.card : ℂ)⁻¹ •
        ∑ g ∈ s, rho g * X * (rho g).conjTranspose) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P23

end
