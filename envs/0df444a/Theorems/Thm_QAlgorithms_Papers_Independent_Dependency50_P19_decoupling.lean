-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_decoupling
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.decoupling
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:11:23.938963+00:00
-- url     : https://prove2.me/theorems/a25b2fbc-b1db-4f1f-ab25-e18732490d4f
-- title:
--   Haar decoupling in squared full trace norm
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   Let $\psi^{RAB}$ and $A=A_1A_2$ be as in the one-shot setting. For a Haar-distributed unitary $U$ on $A$, set $\sigma^{RA_2}(U)=\operatorname{Tr}_{A_1}[(I_R\otimes U)\psi^{RA}(I_R\otimes U)^\dagger]$. Then
--
--   $$
--   \int\!\left\|\sigma^{RA_2}(U)-\sigma^R(U)\otimes\sigma^{A_2}(U)\right\|_1^2\,dU
--   \le\frac{d_A d_R}{d_{A_1}^2}\left[\operatorname{Tr}[(\psi^{RA})^2]+\operatorname{Tr}[(\psi^A)^2]\operatorname{Tr}[(\psi^R)^2]\right].
--   $$
--
--   Haar measure is normalized to total mass one. This bounds an expectation of a square, and does not assert the bound for each unitary.
--
--   It quantifies randomization followed by discarding $A_1$.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 6, Theorem IV.2, Eq. (5)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem IV.2, PDF p.6, Eq.(5): expectation of the squared full trace norm. -/
theorem decoupling {R B : Type*} [Fintype R] [Fintype B]
    [DecidableEq R] [DecidableEq B] [Nonempty R] [Nonempty B]
    (a1 a2 : ℕ) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (psi : EuclideanSpace ℂ (R × (Fin (a1*a2) × B))) (hpsi : IsState psi) :
    (∫ U : Matrix.unitaryGroup (Fin (a1*a2)) ℂ,
      (traceNorm (decouplingDifference a1 a2 (marginalRA (pureDensity psi))
        (U : Matrix _ _ ℂ)))^2 ∂(Schur.unitaryHaar (a1*a2))) ≤
    ((a1*a2 : ℕ) * (Fintype.card R : ℝ) / (a1 : ℝ)^2) *
      (purity (marginalRA (pureDensity psi)) +
        purity (traceLeft (marginalRA (pureDensity psi))) *
          purity (traceRight (marginalRA (pureDensity psi)))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
