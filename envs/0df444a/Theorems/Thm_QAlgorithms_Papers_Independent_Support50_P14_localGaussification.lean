-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Support50_P14_localGaussification
-- name    : QAlgorithms.Papers.Independent.Support50.P14.localGaussification
-- status  : Open
-- author  : @Goku
-- created : 2026-10-23T19:28:43.940555+00:00
-- url     : https://prove2.me/theorems/17de2fc0-818c-4df2-9985-536c696d16cf
-- title:
--   Unnumbered local Gaussification construction, (5)-(11)
-- statement:
--   Let $\rho$ be a normalized density on a nonempty finite collection of full oscillator modes, with zero first moments and finite symmetric covariance $\Gamma$. For $n=2^m$, label the copies by binary strings $k\in\{0,1\}^m$ and use the Sylvester matrix $H_{kl}=(-1)^{k\cdot l}$. There exist bounded unitaries implementing $H/\sqrt n$ on both quadratures of the copies at each site. Their action on $\rho^{\otimes n}$ gives normalized states with computed one-copy marginals $\widetilde\rho_{m,k}$. A normalized Gaussian density $\rho_G$ with moments $(0,\Gamma)$ exists, and
--
--   $$\forall\varepsilon>0\ \exists m_0\ \forall m\ge m_0\ \forall k\in\{0,1\}^m:\quad\|\widetilde\rho_{m,k}-\rho_G\|_1<\varepsilon.$$
--
--   Each marginal has the same moments and characteristic function $\chi(\xi/\sqrt n)^{n_+}\chi(-\xi/\sqrt n)^{n-n_+}$, where $n_+=n$ for the zero row and $n_+=n/2$ otherwise. This construction supplies the local Gaussian limit used by Lemma 1.
-- source:
--   Extremality of Gaussian quantum states, arXiv:quant-ph/0509154v1, PDF p. 2, Unnumbered local Gaussification construction, (5)-(11)

import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

noncomputable section

open Filter

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable Classical.decEq

namespace QAlgorithms.Papers.Independent.Support50.P14

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass traceSize)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel boundedUnitaryConjugation)

open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

open QAlgorithms.Papers.Independent.Gap48.P20 (Copies)

/-- Local Gaussification, PDF p.2, (5)--(11). For a centered finite-energy
input, actual bounded Sylvester copy mixers and their computed normalized
marginals converge in trace norm UNIFORMLY in the growing copy label.
The exact two characteristic-function formulas are retained. -/
theorem localGaussification {I : Type} [Fintype I] [Nonempty I]
    (rho : State (Occupation I)) (gamma : OscillatorCovariance I)
    (hmoments : CompleteMoments rho.coefficients 0 gamma) :
    ∃ rhoG : State (Occupation I), GaussianAt rhoG.coefficients 0 gamma ∧
    ∃ U : (m : ℕ) → Hilbert (Occupation (Copies Bool m)) ≃ₗᵢ[ℂ]
      Hilbert (Occupation (Copies Bool m)),
      (∀ m (xi : InterleavedQuadrature (Copies Bool m) → ℝ),
        boundedUnitaryConjugation (U m).symm (oscillatorWeylKernel xi) = oscillatorWeylKernel (mixedArgument m xi)) ∧
      (∀ m, IsDensity (conjugateKernel (copyMixerKernel m (U m))
        (copiesKernel m rho.coefficients))) ∧
      (∀ m (k : Copies Bool m),
        let reduced := copyMarginal (conjugateKernel (copyMixerKernel m (U m))
          (copiesKernel m rho.coefficients)) k
        IsDensity reduced ∧ CompleteMoments reduced 0 gamma ∧
        ∀ xi : InterleavedQuadrature I → ℝ,
          oscillatorCharacteristic reduced xi =
            oscillatorCharacteristic rho.coefficients (((Real.sqrt ((2 : ℝ) ^ m))⁻¹) • xi) ^
              positiveEntries m k *
            oscillatorCharacteristic rho.coefficients ((-(Real.sqrt ((2 : ℝ) ^ m))⁻¹) • xi) ^
              (2 ^ m - positiveEntries m k)) ∧
      (∀ epsilon : ℝ, 0 < epsilon → ∃ m0 : ℕ, ∀ m : ℕ, m0 ≤ m →
        ∀ k : Copies Bool m,
          traceSize (copyMarginal (conjugateKernel (copyMixerKernel m (U m))
            (copiesKernel m rho.coefficients)) k - rhoG.coefficients) <
              ENNReal.ofReal epsilon) := by sorry

end QAlgorithms.Papers.Independent.Support50.P14

end
