-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P30_globalHaar_dataStatistics
-- name    : QAlgorithms.Papers.Independent.Support50.P30.globalHaar_dataStatistics
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T21:29:14.913977+00:00
-- url     : https://prove2.me/theorems/6ff6f36e-49c1-4955-82dc-4799a0523083
-- title:
--   Unnumbered global-Haar data-statistic identities and scaling
-- statement:
--   Fix orthonormal Schur coordinates for $n$ qubits and a normalized pure seed $\psi$, independently of a Haar unitary $V\in U(D)$, where $D=2^n$. Set $\rho=V|\psi\rangle\langle\psi|V^\dagger$. Write $\Delta(A,B)=\operatorname{Tr}(AB)-\operatorname{Tr}(A)\operatorname{Tr}(B)/d_\lambda$ within a sector. Then
--
--   $$\mathbb E_V[\Delta(\rho_\lambda^\nu,\rho_\lambda^{\nu'})]=
--   \begin{cases}(d_\lambda^2-1)/(D(D+1)),&\nu=\nu',\\0,&\nu\ne\nu',\end{cases}$$
--   $$\mathbb E_V\!\left[\Delta\!\left(\sum_{\nu=1}^{m_\lambda}\rho_\lambda^\nu\right)\right]=\frac{m_\lambda(d_\lambda^2-1)}{D(D+1)}=O\!\left(\frac{n^2}{2^n}\right).$$
--
--   The upper-bound constant and threshold are uniform over sectors, fixed coordinates, and normalized seeds. These are expectations over the input ensemble; they neither assert independence of copies nor bound every Haar draw.
-- source:
--   Theoretical Guarantees for Permutation-Equivariant Quantum Neural Networks, arXiv:2210.09974v3, PDF p. 32, Unnumbered global-Haar data-statistic identities and scaling

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P30

noncomputable section

open MeasureTheory

open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator NNReal ENNReal

namespace QAlgorithms.Papers.Independent.Support50.P30

attribute [local instance] LieRing.ofAssociativeRing

/-- PDF pp.31-32, Eqs.(87),(88), and the uniform sector bound. Different
copies have zero expected pairing; independence of copies is not asserted. -/
theorem globalHaar_dataStatistics :
    (∀ (n : ℕ) (S : SchurFrame n) (m : Sector n)
      (psi : EuclideanSpace ℂ (Qubits n)), IsState psi →
      (∀ nu nuOther : Fin (qnnSectorMultiplicity n m),
        (∫ V, deltaPair (schurCompression S m nu (haarPureInput psi V))
          (schurCompression S m nuOther (haarPureInput psi V)) ∂(QAlgorithms.Schur.unitaryHaar (2 ^ n))) =
          if nu = nuOther then ((blockDim n m : ℝ) ^ 2 - 1) /
            ((2 : ℝ) ^ n * ((2 : ℝ) ^ n + 1)) else 0) ∧
      (∫ V, centeredDelta (aggregate S m (haarPureInput psi V)) ∂(QAlgorithms.Schur.unitaryHaar (2 ^ n))) =
        (qnnSectorMultiplicity n m : ℝ) * ((blockDim n m : ℝ) ^ 2 - 1) /
          ((2 : ℝ) ^ n * ((2 : ℝ) ^ n + 1))) ∧
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ (S : SchurFrame n) (m : Sector n)
      (psi : EuclideanSpace ℂ (Qubits n)), IsState psi →
      (∫ V, centeredDelta (aggregate S m (haarPureInput psi V)) ∂(QAlgorithms.Schur.unitaryHaar (2 ^ n))) ≤
        C * (n : ℝ) ^ 2 / (2 : ℝ) ^ n := by sorry

end QAlgorithms.Papers.Independent.Support50.P30

end
