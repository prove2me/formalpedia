-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P18_conditionalEntropy_conditioningApproximation
-- name    : QAlgorithms.Papers.Independent.Claimed50.P18.conditionalEntropy_conditioningApproximation
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:06:32.862451+00:00
-- url     : https://prove2.me/theorems/2f2696a0-70da-46a4-807b-3391a8a8628e
-- title:
--   Three limits from truncating only the conditioning register
-- statement:
--   Let rho_ABCD be a normalized trace-class state on separable complex systems with H(A),H(B)<infinity. Let P_l be any increasing sequence of finite-rank orthogonal projections on the whole system CD, converging strongly to identity. Normalize the compression by Id_AB tensor P_l to obtain rho_l; at a zero-mass prefix use rho_l=rho. Then
--   $$\begin{aligned}
--   H(A|CD)_{\rho_l}&\longrightarrow H(A|CD)_\rho,\\
--   H(B|CD)_{\rho_l}&\longrightarrow H(B|CD)_\rho,\\
--   H(AB|CD)_{\rho_l}&\longrightarrow H(AB|CD)_\rho.
--   \end{aligned}$$
--
--   These simultaneous limits justify passing common-conditioning subadditivity to infinite conditioning systems. No projection is applied to A or B.
-- source:
--   Quantum conditional entropy for infinite-dimensional systems, arXiv:1004.4519v2, PDF p. 6, §2, unnumbered conditioning-register truncation limit in the proof of subadditivity

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P18

noncomputable section

open Filter

open scoped ENNReal BigOperators

open QAlgorithms.RealRegisters (Hilbert)

open QAlgorithms.Papers.Independent.Dependency50.P33

open QAlgorithms.Papers.Independent.Frontier18.P01

open QAlgorithms.Papers.Independent.Frontier18.P08 (operatorTrace)

attribute [local instance] Classical.propDecidable

namespace QAlgorithms.Papers.Independent.Claimed50.P18

/-- All three conditioning-register truncation limits, PDF pp.6–7.
Projectors act on the whole CD factor; A and B are never projected. -/
theorem conditionalEntropy_conditioningApproximation {A B C D : Type}
    [Countable A] [Countable B] [Countable C] [Countable D]
    (rho : State ((A × B) × (C × D)))
    (hA : homogeneousEntropy (traceSecond (traceSecond rho.coefficients)) < ⊤)
    (hB : homogeneousEntropy (traceFirst (traceSecond rho.coefficients)) < ⊤)
    (P : ProjectionApproximation (C × D)) :
    let cut := fun n => conditioningCompression rho.coefficients (P.projection n)
    Tendsto (fun n => finiteFirstConditionalEntropy (dropMiddle (associateRight (cut n)))) atTop
      (nhds (finiteFirstConditionalEntropy (dropMiddle (associateRight rho.coefficients)))) ∧
    Tendsto (fun n => finiteFirstConditionalEntropy (traceFirst (associateRight (cut n)))) atTop
      (nhds (finiteFirstConditionalEntropy (traceFirst (associateRight rho.coefficients)))) ∧
    Tendsto (fun n => finiteFirstConditionalEntropy (cut n)) atTop
      (nhds (finiteFirstConditionalEntropy rho.coefficients)) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P18

end
