-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P67_proposition4_continuous_swap
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P67.proposition4_continuous_swap
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T09:00:23.403233+00:00
-- url     : https://prove2.me/theorems/467ee4a0-9aac-4135-adba-b22964e3aadc
-- title:
--   Proposition 4: continuous SWAP coupling approximates density-matrix evolution
-- statement:
--   Prepare $n\ge1$ independent reference registers in the same unit vector $\phi$, a system density operator $\rho$, a real coupling $J$, and time $t\ge0$. Let $H=J\sum_{j=1}^n\operatorname{SWAP}_{S,j}$, $H_{\rm eff}=J(n+1)|\phi\rangle\langle\phi|$, and let $\rho(t)$ be the actual system partial trace of the joint evolution. Then
--
--   $$F(\rho(t),e^{-itH_{\rm eff}}\rho e^{itH_{\rm eff}})\ge\frac{n-1}{n+1},\qquad\tfrac12\|\rho(t)-e^{-itH_{\rm eff}}\rho e^{itH_{\rm eff}}\|_1\le\frac6n.$$
--
--   For every normalized pure system input $\psi$, the absolute overlap of $e^{-itH}(|\psi\rangle|\phi\rangle^{\otimes n})$ with $(e^{-itH_{\rm eff}}|\psi\rangle)|\phi\rangle^{\otimes n}$ is at least $(n-1)/(n+1)$. These joint and reduced bounds refer to the same physical evolution.
-- source:
--   Universal Quantum Emulator, arXiv:1606.02734v2, PDF p. 24, Proposition 4: continuous SWAP coupling approximates density-matrix evolution

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P67

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

/-- PDF p.24, Proposition 4, E4–E6: both reduced-state estimates and the absolute
joint overlap. Real subtraction prevents truncation at n=1; n=0 is excluded. -/
theorem proposition4_continuous_swap (phi : EuclideanSpace ℂ I) (hphi : IsState phi)
    (n : ℕ) (hn : 1 ≤ n) (coupling t : ℝ) (ht : 0 ≤ t) :
    (∀ rho : Matrix I I ℂ, IsDensityMatrix rho →
      let actual := traceRight (swapJoint phi n coupling t rho)
      let target := densityConjugation (positivePhaseEvolution (effectiveHamiltonian phi n coupling) (-t)) rho
      ((n : ℝ) - 1) / (n + 1) ≤ rootFidelity actual target ∧ traceDistance actual target ≤ 6 / n) ∧
    (∀ psi : EuclideanSpace ℂ I, IsState psi → ((n : ℝ) - 1) / (n + 1) ≤
      ‖inner ℂ (tensorVec (act (positivePhaseEvolution (effectiveHamiltonian phi n coupling) (-t)) psi)
        (referenceVector phi n)) (act (positivePhaseEvolution (swapHamiltonian n coupling) (-t))
          (tensorVec psi (referenceVector phi n)))‖) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P67

end
