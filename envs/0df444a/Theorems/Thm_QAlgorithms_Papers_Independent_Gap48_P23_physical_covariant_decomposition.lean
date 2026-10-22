-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P23_physical_covariant_decomposition
-- name    : QAlgorithms.Papers.Independent.Gap48.P23.physical_covariant_decomposition
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:41:38.30319+00:00
-- url     : https://prove2.me/theorems/1bacd20d-e564-448b-b220-4313a2b97547
-- title:
--   Corollary 4.5.
-- statement:
--   For $\ell\ge1$, input covariance is with $T^\ell(U)$ and output covariance with $U$, for every $U\in U(2)$. The channel $\Phi_{\rm Tr}^\ell$ embeds through $V^\ell$ and keeps the first qubit; $\Phi_{\rm UNOT}^\ell$ measures the normalized coherent-state POVM and prepares the orthogonal state. Let $D_\ell$ be the explicit real dual Clebsch–Gordan matrix (C.49),(C.54). The unnormalized Choi order is output tensor input.
--
--   Every covariant channel $\Phi$ has a parameter $t\in[0,1]$ with
--   $$\Phi=t\Phi_{\rm Tr}^\ell+(1-t)\Phi_{\rm UNOT}^\ell.$$
--   The statement also identifies the literal polynomial action with the accepted real occupation-coordinate action, and retains covariance of both endpoints.
--
--   This characterizes the physical postprocessing maps used in the template algorithm.
-- source:
--   Quantum majority vote, arXiv:2211.11729v1, PDF p. 30, Corollary 4.5.

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF p.30, Corollary 4.5: equality on every operator, using the actual
Definition 4.3 channels. The concrete polynomial/occupation bridge is included. -/
theorem physical_covariant_decomposition (ell : ℕ) (hell : 1 ≤ ell) :
    (∀ M : Op (Fin 2), polynomialIrrep ell M =
      QAlgorithms.Papers.Independent.Support21.P18.symmetricAction ell M) ∧
    PolynomialCovariant ell (partialTraceChannel ell) ∧ PolynomialCovariant ell (universalNotChannel ell) ∧
    ∀ Phi : Superop (Fin (ell + 1)) (Fin 2), IsChannel Phi → PolynomialCovariant ell Phi →
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ ∀ rho,
        Phi rho = (t : ℂ) • partialTraceChannel ell rho +
          ((1-t : ℝ) : ℂ) • universalNotChannel ell rho := by sorry

end QAlgorithms.Papers.Independent.Gap48.P23

end
