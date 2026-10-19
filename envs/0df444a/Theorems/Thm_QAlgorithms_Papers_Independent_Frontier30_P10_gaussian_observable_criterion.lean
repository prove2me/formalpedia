-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P10_gaussian_observable_criterion
-- name    : QAlgorithms.Papers.Independent.Frontier30.P10.gaussian_observable_criterion
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T09:15:52.217982+00:00
-- url     : https://prove2.me/theorems/fa982b4f-cda2-4d76-a2a6-08da5e07b442
-- title:
--   Gaussian observable existence and uncertainty criterion
-- statement:
--   Let $Z_A=\mathbb R^{2a}$ and $Z_B=\mathbb R^{2b}$ carry the standard symplectic forms $\Delta_A$ and $\Delta_B$, and let $W_A$ be a strongly continuous irreducible Weyl system on a nonzero separable complex Hilbert space $\mathcal H_A$. Use the convention $W_A(z)^*W_A(w)W_A(z)=e^{i\Delta_A(w,z)}W_A(w)$. For an arbitrary real linear map $K:Z_B\to Z_A$ and real symmetric bilinear form $\mu$ on $Z_B$, the candidate function $\phi(w)=W_A(Kw)e^{-\mu(w,w)/2}$ is the characteristic function of a normalized POVM on $Z_B$ if and only if
--
--   $$
--   \mu-\frac{i}{2}K^T\Delta_AK\succeq0.
--   $$
--
--   The matrix inequality is positivity as a complex Hermitian matrix. Singular $K$ and semidefinite noise remain allowed. This criterion constructs a Gaussian observable from its characteristic law instead of defining existence by the inequality.
-- source:
--   Entanglement-breaking channels in infinite dimensions, arXiv:0802.0235v1, PDF p. 8, Unnumbered: Gaussian observable existence criterion (23)

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P10

noncomputable section

open MeasureTheory

open scoped ENNReal ComplexOrder

namespace QAlgorithms.Papers.Independent.Frontier30.P10

open QAlgorithms.Papers.Independent.Dependency50.P10 (Phase)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- Holevo, arXiv:0802.0235v1, PDF p.8, (22)–(23).
The Gaussian formula defines an actual POVM iff its uncertainty matrix is
positive semidefinite. Singular K and semidefinite noise are included. -/
theorem gaussian_observable_criterion [SecondCountableTopology H] [Nontrivial H]
    {a b : ℕ} (W : WeylSystem H a)
    (K : Matrix (Phase a) (Phase b) ℝ)
    (mu : Matrix (Phase b) (Phase b) ℝ)
    (hmu : mu.transpose = mu) :
    (∃ M : HilbertPOVM H (Phase b → ℝ),
      HasCharacteristic M (gaussianCharacteristic W K mu)) ↔
      (observableNoiseMatrix K mu).PosSemidef := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P10

end
