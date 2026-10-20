-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_haarHilbertSchmidt
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.haarHilbertSchmidt
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T14:13:01.816549+00:00
-- url     : https://prove2.me/theorems/9e76fbff-2bd9-4640-9976-dc5dd164e24c
-- title:
--   Exact Hilbert–Schmidt decoupling average
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   In the one-shot pure-source setting, use the state $\sigma^{RA_2}(U)$ defined by unitary randomization and tracing out $A_1$. Write $\|\cdot\|_2$ for the Hilbert–Schmidt norm. Then
--
--   $$
--   \int\|\sigma^{RA_2}-\sigma^R\otimes\sigma^{A_2}\|_2^2\,dU
--   =\frac{d_{A_1}d_{A_2}^2-d_{A_1}}{d_A^2-1}
--   \left[\operatorname{Tr}[(\psi^{RA})^2]-2\operatorname{Tr}\bigl(\psi^{RA}(\psi^R\otimes\psi^A)\bigr)+\operatorname{Tr}[(\psi^R)^2]\operatorname{Tr}[(\psi^A)^2]\right].
--   $$
--
--   All dimensional arithmetic in the coefficient is real. At $d_A=1$ use coefficient zero; the decoupling difference itself is identically zero. The normalized Haar integral is of the squared norm.
--
--   This is an exact second-moment identity, stronger than a norm upper bound.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 7, Lemma IV.4, Eq. (14)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma IV.4, PDF p.7, Eq.(14): exact Hilbert–Schmidt square average.
Every subtraction in the coefficient is real; singleton A has coefficient 0. -/
theorem haarHilbertSchmidt {R B : Type*} [Fintype R] [Fintype B]
    [DecidableEq R] [DecidableEq B] [Nonempty R] [Nonempty B]
    (a1 a2 : ℕ) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (psi : EuclideanSpace ℂ (R × (Fin (a1*a2) × B))) (hpsi : IsState psi) :
    (∫ U : Matrix.unitaryGroup (Fin (a1*a2)) ℂ,
      (frobNorm (decouplingDifference a1 a2 (marginalRA (pureDensity psi))
        (U : Matrix _ _ ℂ)))^2 ∂(Schur.unitaryHaar (a1*a2))) =
    (((a1 : ℝ)*(a2 : ℝ)^2-(a1 : ℝ))/(((a1*a2 : ℕ) : ℝ)^2-1)) *
      (purity (marginalRA (pureDensity psi)) -
       2 * ((marginalRA (pureDensity psi)) * Matrix.kronecker
         (traceRight (marginalRA (pureDensity psi)))
         (traceLeft (marginalRA (pureDensity psi)))).trace.re +
       purity (traceLeft (marginalRA (pureDensity psi))) *
         purity (traceRight (marginalRA (pureDensity psi)))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
