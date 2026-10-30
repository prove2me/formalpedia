-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P46_attenuator_holder
-- name    : QAlgorithms.Papers.Independent.Advance50.P46.attenuator_holder
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:10:33.967865+00:00
-- url     : https://prove2.me/theorems/badee22f-7865-4776-bb19-6588aac6a9ec
-- title:
--   Example 5, attenuator rate (5.13)
-- statement:
--   Let $N|n\rangle=n|n\rangle$ on the full one-mode Fock space. Let $\Lambda_t^{\rm att}$ be the attenuator given by the countable Kraus series on PDF p.27, whose coherent amplitude decays as $e^{-t/2}$. For $0<\alpha\le1$ and $E>0$, put $\zeta_1=1$ and, for $\alpha<1$, $\zeta_\alpha=(2\alpha/(1-\alpha))^{1-\alpha}+2(2\alpha/(1-\alpha))^{-\alpha}$. Then, for all $t,s\ge0$,
--
--   $$\|\Lambda_t^{\rm att}-\Lambda_s^{\rm att}\|_{\diamond,2\alpha}^{N,E}\le4\zeta_\alpha(1-\alpha)^{1-\alpha}\alpha^\alpha E^\alpha|t-s|^\alpha.$$
--
--   The norm takes the supremum over normalized states with every finite ancilla and marginal moment $\operatorname{Tr}(N^{2\alpha}\rho)\le E^{2\alpha}$. The series converges in trace norm on every trace-class input and defines a CPTP channel. This supplies the explicit fractional-moment continuity rate.
-- source:
--   Convergence rates for quantum evolution & entropic continuity bounds in infinite dimensions, arXiv:1810.00863v3, PDF p. 27, Example 5, attenuator rate (5.13)

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

/-- Example 5, PDF p.27, (5.13), using the Kraus/generator parameterization.
The endpoint alpha=1 uses zeta_1=1 and 0^0=1 as prescribed by the limiting formula. -/
theorem attenuator_holder (alpha E : ℝ) (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hE : 0 < E) :
    (∀ t : ℝ, 0 ≤ t →
      QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClassChannel (attenuatorTimeKernel t) ∧
      ∀ X, IsTraceClass X → TraceSums (attenuatorTerm t X) (attenuatorTimeKernel t X)) ∧
    ∀ t s : ℝ, 0 ≤ t → 0 ≤ s →
      diagonalMagnitude numberEigenvalue alpha E (fun X => attenuatorTimeKernel t X - attenuatorTimeKernel s X) ≤
        ENNReal.ofReal (bosonicCoefficient alpha * E ^ alpha * |t - s| ^ alpha) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P46

end
