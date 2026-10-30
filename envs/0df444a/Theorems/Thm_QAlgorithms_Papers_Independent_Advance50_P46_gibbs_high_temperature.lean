-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Advance50_P46_gibbs_high_temperature
-- name    : QAlgorithms.Papers.Independent.Advance50.P46.gibbs_high_temperature
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T22:14:03.830468+00:00
-- url     : https://prove2.me/theorems/aab529f7-c927-495b-8169-f74418989603
-- title:
--   Remark 2 (equivalence of high temperature and high energy)
-- statement:
--   Let $H$ be a semibounded self-adjoint Hamiltonian on an infinite-dimensional separable complex Hilbert space satisfying $\operatorname{Tr}e^{-\beta H}<\infty$ for every $\beta>0$. Count eigenvalues with multiplicity and let $E_0=\inf\sigma(H)$. For every $E>E_0$ the equilibrium equation $\operatorname{Tr}(e^{-\beta H}(H-E))=0$ has exactly one positive solution $\beta(E)$ and defines a normalized finite-entropy Gibbs state. For every sequence $E_n>E_0$,
--
--   $$E_n\longrightarrow\infty\quad\Longleftrightarrow\quad\beta(E_n)\longrightarrow0.$$
--
--   This gives the equivalence of high temperature and high energy used in the subsequent asymptotic analysis. No rate is asserted.
-- source:
--   Convergence rates for quantum evolution & entropic continuity bounds in infinite dimensions, arXiv:1810.00863v3, PDF p. 36, Remark 2 (equivalence of high temperature and high energy)

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

/-- Remark 2 with its defining equation (7.3), PDF p.36: high energy and high
temperature are equivalent, for every sequence of admissible energies. -/
theorem gibbs_high_temperature {I : Type} [Countable I] [Infinite I]
    (H : Spectral.Hamiltonian I) (hG : H.gibbs) :
    (∀ E : ℝ, semiboundedGroundEnergy H < E →
      IsEquilibrium H E (betaAtEnergy H E) ∧
      (∀ beta, IsEquilibrium H E beta → beta = betaAtEnergy H E) ∧
      IsDensity (gibbsCoefficients H E) ∧
      Spectral.homogeneousEntropy (gibbsCoefficients H E) < ⊤) ∧
    (∀ energies : ℕ → ℝ, (∀ n, semiboundedGroundEnergy H < energies n) →
      (Tendsto energies atTop atTop ↔
        Tendsto (fun n => betaAtEnergy H (energies n)) atTop (𝓝 (0 : ℝ)))) := by sorry

end QAlgorithms.Papers.Independent.Advance50.P46

end
