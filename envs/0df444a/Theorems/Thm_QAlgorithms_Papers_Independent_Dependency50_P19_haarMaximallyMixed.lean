-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P19_haarMaximallyMixed
-- name    : QAlgorithms.Papers.Independent.Dependency50.P19.haarMaximallyMixed
-- status  : Proved
-- author  : @Goku
-- created : 2026-10-19T14:14:03.820533+00:00
-- url     : https://prove2.me/theorems/dc2c3eda-f075-4d8f-8c22-656491ada454
-- title:
--   Haar closeness to the maximally mixed marginal
-- statement:
--   All registers are finite dimensional and nonempty, pure sources have unit norm, logarithms and entropies are in bits, and $\|\cdot\|_1$ is the full Schatten trace norm.
--
--   For the same pure source, factorization and post-unitary marginal $\sigma^{A_2}(U)$,
--
--   $$
--   \int\left\|\sigma^{A_2}(U)-\frac{I_{A_2}}{d_{A_2}}\right\|_1^2\,dU
--   \le\frac{d_A}{d_{A_1}^2}\operatorname{Tr}[(\psi^A)^2].
--   $$
--
--   The measure is normalized Haar measure and the norm is the full trace norm, rather than the Hilbert–Schmidt norm used at an intermediate proof step. The left side is zero if $d_{A_2}=1$.
--
--   This guarantees the maximally entangled component needed in the mother target.
-- source:
--   The mother of all protocols: Restructuring quantum information's family tree, arXiv:quant-ph/0606225v1, PDF p. 8, Lemma IV.5

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P19

open MeasureTheory

open QAlgorithms.Papers.Independent.Information100.P32 (purity)

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Lemma IV.5, PDF p.8: the norm is the full Schatten 1-norm, squared. -/
theorem haarMaximallyMixed {R B : Type*} [Fintype R] [Fintype B]
    [DecidableEq R] [DecidableEq B] [Nonempty R] [Nonempty B]
    (a1 a2 : ℕ) (ha1 : 0 < a1) (ha2 : 0 < a2)
    (psi : EuclideanSpace ℂ (R × (Fin (a1*a2) × B))) (hpsi : IsState psi) :
    (∫ U : Matrix.unitaryGroup (Fin (a1*a2)) ℂ,
      (traceNorm (traceLeft (sigma a1 a2 (marginalRA (pureDensity psi))
        (U : Matrix _ _ ℂ)) - ((a2 : ℂ)⁻¹) • (1 : Matrix (Fin a2) (Fin a2) ℂ)))^2
      ∂(Schur.unitaryHaar (a1*a2))) ≤
    ((a1*a2 : ℕ) : ℝ)/(a1 : ℝ)^2 *
      purity (traceLeft (marginalRA (pureDensity psi))) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P19

end
