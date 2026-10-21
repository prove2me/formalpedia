-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P37_gaussian_contraction
-- name    : QAlgorithms.Papers.Independent.Claimed50.P37.gaussian_contraction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:38:33.687098+00:00
-- url     : https://prove2.me/theorems/52e9d508-7d3c-41f9-bb2c-3a9d66d7c0ed
-- title:
--   Finite Gaussian contraction and normalized covariance update
-- statement:
--   Let the input and output contain finitely many bosonic modes, with full oscillator Hilbert spaces and interleaved quadratures. Let $\rho$ be a normalized centered Gaussian input of covariance $G$, and $\chi$ a normalized centered Gaussian resource on the input and output factors, of covariance $\Gamma=\begin{pmatrix}A&C\\ C^T&B\end{pmatrix}$. Covariance means twice the ordinary quadrature covariance, so the vacuum covariance is $I$. Put $R=\operatorname{diag}(1,-1,\ldots,1,-1)$ and form the actual, unnormalized contraction $X=\operatorname{Tr}_{\rm in}[\chi(\rho^T\otimes I)]$, where transpose is in the number basis. Then $A+RGR$ is positive definite, $X$ is trace class, and $p=\operatorname{Tr}X>0$. The density $X/p$ is centered Gaussian with
--
--   $$
--   \Gamma_{\rm out}=B-C^T(A+RGR)^{-1}C.
--   $$
--
--   Write $W$ for the Wigner function and $C(q)=\operatorname{Tr}[\rho e^{ir\cdot q}]$ for the characteristic function, with $C_\rho(q)=e^{-q^TGq/4}$. If $n$ is the number of input modes, the unnormalized output also satisfies
--
--   $$
--   W_X(r_o)=(2\pi)^n\int W_\chi(r_i,r_o)W_\rho(Rr_i)\,dr_i,
--   \qquad
--   C_X(q_o)=(2\pi)^{-n}\int C_\chi(q_i,q_o)C_\rho(-Rq_i)\,dq_i.
--   $$
--
--   The displayed integrals are Lebesgue integrals with integrable integrands; the characteristic trace series and output diagonal trace converge. This is the finite-resource calculation underlying the paper's covariance update.
-- source:
--   Gaussian transformations and distillation of entangled Gaussian states, arXiv:quant-ph/0204069v2, PDF p. 2, Eqs.(1),(3)–(7)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P37

noncomputable section

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Claimed50.P37

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass productCoeff)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

/-- Fiurasek, arXiv:quant-ph/0204069v2, PDF pp.1–2, Eqs.(1),(3)–(7).
Centered finite normal Gaussian resource and input densities have a trace-class
contraction with positive success trace. Its normalized output is Gaussian with
covariance B-C^T(A+R G R)^(-1)C. The unnormalized output obeys Eqs.(4),(6),
with the printed constants. There is no universal finite-Choi assertion here. -/
theorem gaussian_contraction {ni no : ℕ}
    (rho : State (FockLabel ni)) (chi : State (FockLabel ni × FockLabel no))
    (G A : Matrix (Quadrature ni) (Quadrature ni) ℝ)
    (B : Matrix (Quadrature no) (Quadrature no) ℝ)
    (C : Matrix (Quadrature ni) (Quadrature no) ℝ)
    (hinput : HasCenteredGaussian rho.coefficients G)
    (hresource : HasCenteredGaussianResource chi.coefficients A B C) :
    let X := contraction chi.coefficients rho.coefficients
    (A + reflection ni * G * reflection ni).PosDef ∧
    IsTraceClass X ∧ Summable (fun a => (X a a).re) ∧
    0 < successTrace X ∧ IsDensity (normalizeFockCoefficients X) ∧
    HasCenteredGaussian (normalizeFockCoefficients X) (outputCovariance G A B C) ∧
    (∀ q : PhaseCoordinates no,
      (∀ a, Summable (fun b => X a b * weylCoeff q b a)) ∧
      Summable (fun a => ∑' b, X a b * weylCoeff q b a)) ∧
    (∀ r : PhaseCoordinates no,
      Integrable (fun q : PhaseCoordinates no => multimodeCharacteristic X q *
        Complex.exp (-Complex.I * (phasePairing r q : ℂ)))) ∧
    (∀ r : PhaseCoordinates no,
      Integrable (fun s : PhaseCoordinates ni => pairWigner chi.coefficients s r *
        wigner rho.coefficients ((reflection ni).mulVec s)) ∧
      wigner X r = (2 * Real.pi : ℂ) ^ ni *
        ∫ s : PhaseCoordinates ni, pairWigner chi.coefficients s r *
          wigner rho.coefficients ((reflection ni).mulVec s)) ∧
    (∀ q : PhaseCoordinates no,
      Integrable (fun s : PhaseCoordinates ni => pairCharacteristic chi.coefficients s q *
        multimodeCharacteristic rho.coefficients (-((reflection ni).mulVec s))) ∧
      multimodeCharacteristic X q = ((2 * Real.pi : ℂ) ^ ni)⁻¹ *
        ∫ s : PhaseCoordinates ni, pairCharacteristic chi.coefficients s q *
          multimodeCharacteristic rho.coefficients (-((reflection ni).mulVec s))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P37

end
