-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P45_fock_schmidt_minimizes_epr
-- name    : QAlgorithms.Papers.Independent.Next46.P45.fock_schmidt_minimizes_epr
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:48:39.670239+00:00
-- url     : https://prove2.me/theorems/7cba9b36-4ad6-40e9-bd24-4dc7344bf0f5
-- title:
--   Fock Schmidt vectors minimize EPR uncertainty
-- statement:
--   Let $\psi$ be a normalized two-mode pure state with the actual expansion $\psi=\sum_{N\ge0}c_Nu_N\otimes v_N$, where $(u_N)$ and $(v_N)$ are complete orthonormal bases of the two full oscillator spaces. The real sequence $c$ lies in $\mathcal C$: $c_N\ge c_{N+1}\ge0$ and $\sum_Nc_N^2=1$. Define the convergent nonnegative EPR sequence functional by $\delta(c)=\sum_{N\ge0}(N+1)(c_N-c_{N+1})^2$, equivalently Eq. (7) on $\mathcal C$. Let $\Delta(\psi)$ be the clipped EPR variance uncertainty, with infinite variance outside each observable domain. Then
--
--   $$\Delta(\psi)\ge\delta(c).$$
--
--   The estimate compares all such Schmidt bases against the Fock ordering for the same coefficients. It does not assume that every infinite-dimensional vector admits this particular complete-basis indexing, and does not require finite photon-number expectation.
--
--   The Fock-ordered state attains the bound: there exists a normalized vector $\phi$ with coefficients $\phi_{m,k}=c_m$ if $m=k$ and zero otherwise, and $\Delta(\phi)=\delta(c)$. This is the exact Fock vector specified by the coefficients, with no finite-energy assumption.
-- source:
--   Entanglement of formation for symmetric Gaussian states, arXiv:quant-ph/0304042v1, PDF p. 2, Lemma 1 and immediately preceding Fock-attainment assertion

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P45

noncomputable section

open MeasureTheory Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P45

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (rankOne IsBarycenter)

open QAlgorithms.Papers.Independent.Claimed50.P19
  (Cov DensityKernel GaussianWithCovariance standardFormCovariance productWeyl
   CharacteristicSummable multimodeWeylTrace covarianceCharacteristicValue)

open QAlgorithms.Papers.Independent.Claimed50.P35 (spectralEntropyBits InterleavedPhase)

local instance : MeasurableSpace TwoMode := borel TwoMode

/-- PDF p.2, Lemma 1 and the immediately preceding Fock-attainment assertion,
with (5),(7). The two complete bases and the actual Schmidt expansion are
hypotheses. The explicitly specified normalized Fock vector attains delta(c).
No universal complete-basis indexing or finite-number expectation is imposed. -/
theorem fock_schmidt_minimizes_epr
    (psi : PureVector) (c : ℕ → ℝ) (hc : SchmidtClass c)
    (u v : HilbertBasis ℕ ℂ (Hilbert ℕ))
    (hexpansion : ∀ i : Fin 2 → ℕ,
      HasSum (fun j : ℕ => (c j : ℂ) * u j (i 0) * v j (i 1)) (psi.val i)) :
    sequenceUncertainty c ≤ ENNReal.ofReal (eprUncertainty psi.val) ∧
    ∃ phi : PureVector,
      (∀ i : Fin 2 → ℕ,
        phi.val i = if i 0 = i 1 then (c (i 0) : ℂ) else 0) ∧
      ENNReal.ofReal (eprUncertainty phi.val) = sequenceUncertainty c := by sorry

end QAlgorithms.Papers.Independent.Next46.P45

end
