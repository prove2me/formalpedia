-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Bridge50_P16_fidelityBilinear
-- name    : QAlgorithms.Papers.Independent.Bridge50.P16.fidelityBilinear
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T14:47:25.520503+00:00
-- url     : https://prove2.me/theorems/c41f860b-73a6-414e-a39f-c41f5dd959d7
-- title:
--   Section V B, Eqs.(62)–(65): entanglement fidelity is bilinear in Choi matrices
-- statement:
--   Let $1\le d\le n$, and let $\mathcal E:\mathbb C^d\to\mathbb C^n$, $\mathcal N:\mathbb C^n\to\mathbb C^n$, and $\mathcal D:\mathbb C^n\to\mathbb C^d$ be CPTP maps on operators. In fixed orthonormal bases define the unnormalized input-first Choi matrix by $X_{\mathcal A}[(i,j),(i',j')]=\langle j|\mathcal A(|i\rangle\langle i'|)|j'\rangle$. Define the linear contraction
--
--   $$f_{\mathcal N}(X)[(l',i'),(l,i)]=\sum_{k,k'=0}^{n-1}X_{\mathcal N}[(k,l),(k',l')]X[(i,k),(i',k')].$$
--
--   For the squared overlap with the normalized maximally entangled logical state,
--
--   $$F_e(\mathcal D\mathcal N\mathcal E)=\frac{1}{d^2}\operatorname{Tr}\!\left[X_{\mathcal D}f_{\mathcal N}(X_{\mathcal E})\right].$$
--
--   The real trace objective extends to a real bilinear function of arbitrary encoding and decoding Choi matrices. This supplies the linear objective in each SDP slice.
-- source:
--   Improved quantum capacity bounds of Gaussian loss channels and achievable rates with Gottesman-Kitaev-Preskill codes, arXiv:1801.07271v2, PDF p. 12, Section V B, Eqs.(62)–(65): entanglement fidelity is bilinear in Choi matrices

import Definitions.Def_QAlgorithms_Papers_Independent_Bridge50_P16

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal NNReal Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Bridge50.P16

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Frontier30.P08 (interleavedSymplecticForm)

open QAlgorithms.Papers.Independent.Dependency50.P30 (thermalEntropyBits)

open QAlgorithms.Papers.Independent.Frontier18.P18 (operatorCoeff boundedOperator)

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Dependency50.P32 (CPTP applyChoi)

/-- PDF p.12 Eqs.(62)--(65). Printed prose duplicates XE; changed to XE and XD
because Eq.(63) explicitly depends on those two distinct Choi matrices. -/
theorem fidelityBilinear {d n : ℕ} (hd : 0 < d) (hdn : d ≤ n)
    (E : Superop (Fin d) (Fin n)) (N : Superop (Fin n) (Fin n))
    (D : Superop (Fin n) (Fin d)) (hE : IsChannel E) (hN : IsChannel N) (hD : IsChannel D) :
    QuditFidelity.entanglementFidelity d hd (D ∘ N ∘ E) =
      jointObjective N (choi E) (choi D) / (d : ℝ) ^ 2 ∧
    ∃ L : Matrix (Fin d × Fin n) (Fin d × Fin n) ℂ →ₗ[ℝ]
        (Matrix (Fin n × Fin d) (Fin n × Fin d) ℂ →ₗ[ℝ] ℝ),
      ∀ XE XD, L XE XD = jointObjective N XE XD := by sorry

end QAlgorithms.Papers.Independent.Bridge50.P16

end
