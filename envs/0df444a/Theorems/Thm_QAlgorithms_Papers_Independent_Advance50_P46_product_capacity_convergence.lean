-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P46_product_capacity_convergence
-- name    : QAlgorithms.Papers.Independent.Advance50.P46.product_capacity_convergence
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:08:39.133191+00:00
-- url     : https://prove2.me/theorems/c32bfc48-ebb1-4b6a-a6a8-50ea6f9ac9c7
-- title:
--   Proposition [Capacity convergence], product-state bound
-- statement:
--   Let $H_A\ge0$ be an arbitrary positive self-adjoint input observable and let $H_B\ge0$ satisfy the Gibbs hypothesis and spectral-pair ratio condition with exponent $\eta$. For $E>\inf\sigma(H_A)$ and $0<\varepsilon<1$, let CPTP channels $\Phi,\Psi$ satisfy $\tfrac12\|\Phi-\Psi\|_\diamond^{H_A,E}\le\varepsilon$. Suppose one positive function $k$ bounds both output energies by $k(E)E$ for every state of input energy at most $E$. Define $r=(1+t/2)/(1-\varepsilon t)$, $g(x)=(x+1)\log(x+1)-x\log x$, and binary entropy $h$. For $0<t\le1/(2\varepsilon)$,
--
--   $$|C^{(1)}(\Phi,H_A,E)-C^{(1)}(\Psi,H_A,E)|\le\varepsilon(2t+r)F_{H_B}\!\left(\frac{k(E)E}{\varepsilon t}\right)+2g(\varepsilon r)+2h(\varepsilon t).$$
--
--   The capacities are finite suprema over countably discrete ensembles with barycenter energy strictly below $E$. Individual signals need not satisfy the energy bound. The maximum-entropy envelope satisfies $F_{H_B}(x)=\eta\log x(1+R_{H_B}(x))$ at high arguments, with a common remainder tending to zero. This is the product-state bound only.
-- source:
--   Convergence rates for quantum evolution & entropic continuity bounds in infinite dimensions, arXiv:1810.00863v3, PDF p. 16, Proposition [Capacity convergence], product-state bound

import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P46

noncomputable section

open MeasureTheory Filter

open scoped ENNReal NNReal Topology BigOperators Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Advance50.P46

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Bridge50.P23 (energyMagnitude numberEnergy)

open QAlgorithms.Papers.Independent.Dependency50.P33
  (State IsDensity IsTraceClass traceSize rankOne tensorApply productCoeff IsBarycenter)

attribute [local instance] Classical.propDecidable Classical.decEq

export QAlgorithms.Papers.Independent.Claimed50.P39 (g)

/-- Proposition [Capacity convergence], PDF pp.16,44, first inequality (3.18).
Both channels share the same positive output-energy function, applied to all
input states with energy <=E. The capacity uses countably discrete ensembles
with strictly smaller average energy, not individual signal constraints. -/
theorem product_capacity_convergence {I J : Type} [Countable I] [Infinite I]
    [Countable J] [Infinite J] (F : Forms.PositiveObservable I)
    (H : Spectral.Hamiltonian J) (hpos : ∀ j, 0 ≤ H.energy j) (hG : H.gibbs)
    (xi : ℝ) (hxi : HasPairRatio H xi)
    (Phi Psi : Spectral.Channel I J) (E epsilon : ℝ) (hE : formGround F < E)
    (heps : 0 < epsilon) (heps1 : epsilon < 1)
    (hdist : energyMagnitude F E (fun X => Phi.val X - Psi.val X) ≤
      ENNReal.ofReal (2 * epsilon))
    (k : ℝ → ℝ) (hk : ∀ x : ℝ, 0 < x → 0 < k x)
    (hout : ∀ rho : State I,
      Forms.closedFormExpectation F rho.coefficients ≤ ENNReal.ofReal E →
      realSpectrumMeanEnergy H.energy (Phi.val rho.coefficients) ≤ ENNReal.ofReal (k E * E) ∧
      realSpectrumMeanEnergy H.energy (Psi.val rho.coefficients) ≤ ENNReal.ofReal (k E * E)) :
    ThermalAsymptotic H xi ∧ countableProductHolevoCapacity Phi F E < ⊤ ∧ countableProductHolevoCapacity Psi F E < ⊤ ∧
    ∀ t : ℝ, 0 < t → t ≤ 1 / (2 * epsilon) →
      |(countableProductHolevoCapacity Phi F E).toReal - (countableProductHolevoCapacity Psi F E).toReal| ≤
        holevoModulus H (k E * E) epsilon t := by sorry

end QAlgorithms.Papers.Independent.Advance50.P46

end
