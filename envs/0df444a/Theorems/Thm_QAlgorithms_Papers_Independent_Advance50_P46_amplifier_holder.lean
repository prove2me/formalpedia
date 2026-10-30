-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P46_amplifier_holder
-- name    : QAlgorithms.Papers.Independent.Advance50.P46.amplifier_holder
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:12:03.974989+00:00
-- url     : https://prove2.me/theorems/80017d89-8169-4aab-9205-120de4c711ae
-- title:
--   Example 5, amplifier bounds with M and N constraints
-- statement:
--   On one-mode Fock space let $N|n\rangle=n|n\rangle$ and $M=N+I$. Let $\Lambda_t^{\rm amp}$ be the quantum-limited amplifier with amplitude gain $e^{t/2}$, defined by its raising-shift Kraus matrices. Write $b_\alpha=4\zeta_\alpha(1-\alpha)^{1-\alpha}\alpha^\alpha$, with $\zeta_\alpha$ as in (3.1). For $0<\alpha\le1$ and $t,s\ge0$,
--
--   $$\|\Lambda_t^{\rm amp}-\Lambda_s^{\rm amp}\|_{\diamond,2\alpha}^{M,E}\le b_\alpha E^\alpha|t-s|^\alpha\quad(E>1),$$
--   $$\|\Lambda_t^{\rm amp}-\Lambda_s^{\rm amp}\|_{\diamond,2\alpha}^{N,E}\le b_\alpha\sqrt{2E^{2\alpha}+2}\,|t-s|^\alpha\quad(E>0).$$
--
--   Each norm includes every finite ancilla and the stated marginal moment constraint. The Kraus series converges in trace norm and defines a CPTP channel. These are the two distinct energy-observable bounds from Example 5.
-- source:
--   Convergence rates for quantum evolution & entropic continuity bounds in infinite dimensions, arXiv:1810.00863v3, PDF p. 27, Example 5, amplifier bounds with M and N constraints

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

/-- Example 5, PDF p.28: both M and N constraints, with their distinct ground energies. -/
theorem amplifier_holder (alpha : ℝ) (ha : 0 < alpha) (ha1 : alpha ≤ 1) :
    (∀ t : ℝ, 0 ≤ t →
      QAlgorithms.Papers.Independent.Dependency50.P33.IsTraceClassChannel (amplifierTimeKernel t) ∧
      ∀ X, IsTraceClass X → TraceSums (amplifierTerm t X) (amplifierTimeKernel t X)) ∧
    (∀ E : ℝ, 1 < E → ∀ t s : ℝ, 0 ≤ t → 0 ≤ s →
      diagonalMagnitude amplifierEnergy alpha E (fun X => amplifierTimeKernel t X - amplifierTimeKernel s X) ≤
        ENNReal.ofReal (bosonicCoefficient alpha * E ^ alpha * |t - s| ^ alpha)) ∧
    (∀ E : ℝ, 0 < E → ∀ t s : ℝ, 0 ≤ t → 0 ≤ s →
      diagonalMagnitude numberEigenvalue alpha E (fun X => amplifierTimeKernel t X - amplifierTimeKernel s X) ≤
        ENNReal.ofReal (bosonicCoefficient alpha * Real.sqrt (2 * E ^ (2 * alpha) + 2) *
          |t - s| ^ alpha)) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P46

end
