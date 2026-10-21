-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P37_local_map_factorization
-- name    : QAlgorithms.Papers.Independent.Claimed50.P37.local_map_factorization
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:39:42.693156+00:00
-- url     : https://prove2.me/theorems/fad65810-bd12-4fc6-a03c-66023045553f
-- title:
--   Constructed local resource factorization with normalized successful outputs
-- statement:
--   Let $\chi$ be a normalized pure Gaussian resource with two local input modes and one local output mode, on full oscillator spaces. There exist a squeezed-pair parameter $r\ge0$, symplectic unitaries $U_i,U_o$ on the input and output factors, and displacement operators $D_i,D_o$, giving the preceding preparation of $\chi$. Set $V_i=D_iU_i$ and construct $\chi_0$ from the corresponding two-mode squeezed pair by applying $D_oU_o$ to its output. Thus $\chi_0$ is a density operator on one input and one output mode. Define $\mathcal M_\eta(Z)=\operatorname{Tr}_{\rm in}[\eta(Z^T\otimes I)]$ for a resource $\eta$. For every normalized two-mode input density $\rho$, put $\tau=\langle0|_{i_2}V_i^T\rho\overline{V_i}|0\rangle_{i_2}$. Then
--
--   $$
--   \mathcal M_\chi(\rho)=\mathcal M_{\chi_0}(\tau).
--   $$
--
--   If $\operatorname{Tr}\mathcal M_\chi(\rho)>0$, then $\tau$ is trace class with summable diagonal and $\operatorname{Tr}\tau>0$, both successful final outputs are normalized densities, and
--
--   $$
--   \frac{\mathcal M_\chi(\rho)}{\operatorname{Tr}\mathcal M_\chi(\rho)}
--   =
--   \frac{\mathcal M_{\chi_0}(\tau/\operatorname{Tr}\tau)}{\operatorname{Tr}\mathcal M_{\chi_0}(\tau/\operatorname{Tr}\tau)}.
--   $$
--
--   Transpose and conjugation here are those of operators in the fixed number basis. The resource factorization is constructed from $\chi$ before $\rho$ is chosen. The result applies separately to either party's local resource.
-- source:
--   Gaussian transformations and distillation of entangled Gaussian states, arXiv:quant-ph/0204069v2, PDF p. 4, Eqs.(12),(13), steps (i)–(iii)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P37

noncomputable section

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Claimed50.P37

open QAlgorithms.Papers.Independent.Information100.P37 (quadratic)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass productCoeff)

open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33 (PureState rankOne)

open QAlgorithms.Papers.Independent.Frontier30.P14
  (unitaryCoeff conjugateKernel composeKernel)

open QAlgorithms.Papers.Independent.Frontier30.P14 (identityCoeff)

/-- Fiurasek, arXiv:quant-ph/0204069v2, PDF p.4, Eqs.(12),(13).
Every normal pure local three-mode Gaussian resource admits the constructed
three-step factorization: operator-transpose input unitary, vacuum projection,
and residual one-input/one-output Gaussian map. First moments are restored by
local Weyl displacements. The identity is for unnormalized maps; successful
outputs and the intermediate projection are explicitly normalized separately.
The same statement applies independently to Alice's or Bob's local resource. -/
theorem local_map_factorization
    (chi : PureState (FockLabel 2 × FockLabel 1))
    (hgaussian : IsGaussianPair chi.val.coefficients) :
    ∃ (r : ℝ)
      (Ui : Hilbert (FockLabel 2) ≃ₗᵢ[ℂ] Hilbert (FockLabel 2))
      (Uo : Hilbert (FockLabel 1) ≃ₗᵢ[ℂ] Hilbert (FockLabel 1))
      (di : PhaseCoordinates 2) (dout : PhaseCoordinates 1),
      0 ≤ r ∧ IsSymplecticUnitary Ui ∧ IsSymplecticUnitary Uo ∧
      chi.val.coefficients = normalFormPreparation Ui Uo di dout r ∧
      IsDensity (residualResource Uo dout r) ∧
      ∀ rho : State (FockLabel 2),
        let tau := vacuumProjection (transposedInput Ui di rho.coefficients)
        let Y := contraction chi.val.coefficients rho.coefficients
        Y = contraction (residualResource Uo dout r) tau ∧
        (0 < successTrace Y →
          IsTraceClass tau ∧ Summable (fun a => (tau a a).re) ∧
          0 < successTrace tau ∧ IsDensity (normalizeFockCoefficients tau) ∧
          0 < successTrace (contraction (residualResource Uo dout r) (normalizeFockCoefficients tau)) ∧
          IsDensity (normalizeFockCoefficients Y) ∧
          normalizeFockCoefficients Y = normalizeFockCoefficients
            (contraction (residualResource Uo dout r) (normalizeFockCoefficients tau))) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P37

end
