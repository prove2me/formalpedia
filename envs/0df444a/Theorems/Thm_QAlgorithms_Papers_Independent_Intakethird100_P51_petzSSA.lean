-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P51_petzSSA
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P51.petzSSA
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T05:49:08.279605+00:00
-- url     : https://prove2.me/theorems/620a18ee-f77f-4df8-b7b7-076e40920beb
-- title:
--   Section 2.3: equivalence with Petz imaginary-power condition and intertwining
-- statement:
--   For a faithful normalized tripartite state, let $L_{12},L_{23},L_2$ denote the logarithms of its actual marginals lifted by identity operators. Equality in SSA is equivalent to $\log\rho_{123}-L_{12}=L_{23}-L_2$, and also to
--   $$e^{itL_{12}}e^{-itL_2}=e^{it\log\rho_{123}}e^{-itL_{23}}\quad(t\in\mathbb R).$$
--   Any of these conditions implies
--   $$e^{it(L_{12}-L_2+L_{23})}=e^{itL_{12}}e^{-itL_2}e^{itL_{23}}\quad(t\in\mathbb R).$$
--   This identifies the logarithm criterion with Petz’s imaginary-power condition and records its intertwining consequence.
-- source:
--   Inequalities for Quantum Entropy: A Review with Conditions for Equality, arXiv:quant-ph/0205064v2, PDF p. 7, Section 2.3: equivalence with Petz imaginary-power condition and intertwining

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P51

noncomputable section

open scoped Matrix ComplexOrder ComplexConjugate Matrix.Norms.L2Operator

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Intakethird100.P51

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact interfaces from the frozen accepted library; no local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy holevo IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (average)

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy marginalAB channelAdjoint)

open QAlgorithms.Papers.Independent.Dependency50.P35 (marginalAC)

open QAlgorithms.Papers.Independent.Gap48.P19 (shannonNats)

open QAlgorithms.Papers.Independent.Gap48.P33 (measurementInformation)

section Statements

variable {A B C D J K O : Type}

variable [Fintype A] [Fintype B] [Fintype C] [Fintype D] [Fintype J] [Fintype K] [Fintype O]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

variable [DecidableEq J] [DecidableEq K] [DecidableEq O]

/-- Section 2.3, equations (13)–(15), PDF p.7: every real imaginary-power parameter. -/
theorem petzSSA [Nonempty A] [Nonempty B] [Nonempty C] (rho : Mat (A × (B × C))) (h : FaithfulDensity rho) :
    let L12 := liftAB (logMatrix (marginalAB rho))
    let L23 := liftBC (logMatrix (traceLeft rho))
    let L2 := liftB (logMatrix (traceRight (traceLeft rho)))
    let P := ∀ t : ℝ, imaginaryExp t L12 * imaginaryExp (-t) L2 =
      imaginaryExp t (logMatrix rho) * imaginaryExp (-t) L23
    (ssaGap rho = 0 ↔ SSAlogCondition rho) ∧ (SSAlogCondition rho ↔ P) ∧
    (ssaGap rho = 0 → ∀ t : ℝ, imaginaryExp t (L12 - L2 + L23) =
      imaginaryExp t L12 * imaginaryExp (-t) L2 * imaginaryExp t L23) := by sorry

end Statements

end QAlgorithms.Papers.Independent.Intakethird100.P51

end
