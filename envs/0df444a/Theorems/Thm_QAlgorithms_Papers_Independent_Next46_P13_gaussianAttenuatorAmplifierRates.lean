-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P13_gaussianAttenuatorAmplifierRates
-- name    : QAlgorithms.Papers.Independent.Next46.P13.gaussianAttenuatorAmplifierRates
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T14:13:37.986451+00:00
-- url     : https://prove2.me/theorems/0d01e30e-167b-4651-b10e-a8310227ddcc
-- title:
--   Lemma 11, (80): Gaussian attenuator/amplifier rates
-- statement:
--   Let $\rho$ be a centered one-mode Gaussian state with trivial kernel and covariance $M_{jk}=\operatorname{tr}(\rho\{R_j,R_k\})$, where $[Q,P]=i$. Suppose $M=\kappa S^TS$, with $\kappa>1$, $S=O_1\operatorname{diag}(z,z^{-1})O_2^T$, $z\ge1$, and both $O_i$ orthogonal and symplectic. For the canonical attenuator and amplifier generators $L_-$ and $L_+$, both right entropy derivatives exist and are finite. Writing $J_\pm(\rho)=2\left.\frac d{dt}S(e^{tL_\pm}\rho)\right|_{0+}$, one has
--
--   $$J_\pm(\rho)=\left(\frac{z^2+z^{-2}}2\pm\kappa\right)
--   \left[\log\frac{\kappa+1}2-\log\frac{\kappa-1}2\right].$$
--
--   This includes all rotations and squeezing. The occupation $(\kappa-1)/2$ is the thermal symplectic occupation. For a squeezed centered state its physical photon mean is $(\operatorname{tr}M-2)/4$.
--
--   **Formalization Note** The printed phrase identifying $\kappa=2n+1$ with physical photon mean is corrected using the proof (83)–(84); interpreting it literally would remove squeezed states. The Lean conclusion gives the entropy derivatives themselves, half of the displayed $J_\pm$.
-- source:
--   Geometric inequalities from phase space translations, arXiv:1606.08603v2, PDF p. 32, Lemma 11, (80)

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P13

noncomputable section

open Filter MeasureTheory

open scoped BigOperators ENNReal Topology

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

namespace QAlgorithms.Papers.Independent.Next46.P13

/-- PDF pp.32–33, Lemma 11, (80). SOURCE CORRECTION: the printed n in
kappa=2n+1 is thermal symplectic occupation, not physical photon mean of a
squeezed state. The proof (83)–(84) uses kappa this way; actual centered mean is
(tr M-2)/4. Both signs retain ((z^2+z^(-2))/2 plus or minus kappa), as printed. -/
theorem gaussianAttenuatorAmplifierRates (X : B.FockOperator)
    (hgaussian : C.IsGaussian X) (hfull : HasTrivialKernel X) (hcentered : C.meanA X = 0)
    (kappa z : ℝ) (hkappa : 1 < kappa) (hz : 1 ≤ z)
    (O1 O2 : Matrix (Fin 2) (Fin 2) ℝ)
    (hO1 : OrthogonalSymplectic O1) (hO2 : OrthogonalSymplectic O2)
    (hcov : quadratureCovariance X = kappa •
      ((O1 * squeeze z * O2.transpose).transpose * (O1 * squeeze z * O2.transpose))) :
    C.fockEntropyNats X ≠ ⊤ ∧
    (∀ t : ℝ, 0 ≤ t → ThermalChannelRealized (Real.exp (-t)) 0 X ∧
      AmplifierOutputRealized t X ∧ C.fockEntropyNats (attenuator t X) ≠ ⊤ ∧ C.fockEntropyNats (amplifierFlow t X) ≠ ⊤) ∧
    HasDerivWithinAt (fun t : ℝ => entropyReal (attenuator t X))
      (((z ^ 2 + z⁻¹ ^ 2) / 2 - kappa) *
        (Real.log ((kappa + 1) / 2) - Real.log ((kappa - 1) / 2)) / 2) (Set.Ici 0) 0 ∧
    HasDerivWithinAt (fun t : ℝ => entropyReal (amplifierFlow t X))
      (((z ^ 2 + z⁻¹ ^ 2) / 2 + kappa) *
        (Real.log ((kappa + 1) / 2) - Real.log ((kappa - 1) / 2)) / 2) (Set.Ici 0) 0 := by sorry

end QAlgorithms.Papers.Independent.Next46.P13

end
