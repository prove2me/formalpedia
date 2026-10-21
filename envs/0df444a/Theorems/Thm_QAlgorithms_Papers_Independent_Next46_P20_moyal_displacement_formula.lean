-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P20_moyal_displacement_formula
-- name    : QAlgorithms.Papers.Independent.Next46.P20.moyal_displacement_formula
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T15:27:26.50245+00:00
-- url     : https://prove2.me/theorems/a2ff1185-34c0-4874-92ce-68c9af30be4b
-- title:
--   Moyal displacement as a unitary half-shift
-- statement:
--   Let $n\ge1$ and $z_0=(x_0,\xi_0)\in\mathbb R^{2n}$. Let $T_{PS}(z_0)\Psi(x,p)=e^{i(\xi_0\cdot x-\xi_0\cdot x_0/2)}\Psi(x-x_0,p)$ and define $\widetilde T_M(z_0)=U T_{PS}(z_0)U^{-1}$. Then $\widetilde T_M(z_0)$ is unitary and, for every phase-space $L^2$ vector,
--   $$
--   (\widetilde T_M(z_0)\Psi)(x,p)=e^{-i(x_0\cdot p-\xi_0\cdot x)}\Psi(x-x_0/2,p-\xi_0/2)
--   $$
--   almost everywhere.
--
--   There is no additional displacement self-phase in this formula.
-- source:
--   Quantum mechanics in phase space: The Schr\"odinger and the Moyal representations, arXiv:1209.1850v1, PDF p. 23, Theorem 5.6

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P20

noncomputable section

attribute [local instance] Classical.propDecidable

open MeasureTheory

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Next46.P20

open QAlgorithms.Papers.Independent.Claimed50.P10 (Configuration coordinateDot)

open QAlgorithms.Papers.Independent.Claimed50.P05 (restrictGraph)

open QAlgorithms.Papers.Independent.Claimed50.P37 (PhaseCoordinates)

/-- PDF p.23, Theorem 5.6: conjugated displacement is the unitary half-shift
with phase exp(-i(x0 dot p-xi0 dot x)), for every displacement and L2 input. -/
theorem moyal_displacement_formula {n : ℕ} (hn : 0 < n) (d : PhaseCoordinates n) :
    RealizesL2Formula (phaseDisplacementFormula d) (phaseDisplacement d) ∧
    unitaryL2 (moyalDisplacement d) ∧
    (∀ f : PhaseL2 n, ∀ᵐ z : PhaseCoordinates n,
      moyalDisplacement d f z =
        Complex.exp (-Complex.I * ((coordinateDot (phasePosition d) (phaseMomentum z) - coordinateDot (phaseMomentum d) (phasePosition z) : ℝ) : ℂ)) *
          f (phasePoint ((phasePosition z) - (1 / 2 : ℝ) • (phasePosition d)) ((phaseMomentum z) - (1 / 2 : ℝ) • (phaseMomentum d)))) := by sorry

end QAlgorithms.Papers.Independent.Next46.P20

end
