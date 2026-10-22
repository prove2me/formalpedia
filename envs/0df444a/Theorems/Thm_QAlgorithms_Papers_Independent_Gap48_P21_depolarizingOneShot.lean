-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P21_depolarizingOneShot
-- name    : QAlgorithms.Papers.Independent.Gap48.P21.depolarizingOneShot
-- status  : Open
-- author  : @Goku
-- created : 2026-10-21T22:13:52.084183+00:00
-- url     : https://prove2.me/theorems/dce2b885-e418-4165-9c02-9a03b7824674
-- title:
--   Equation (1): one-shot accessible capacity and attaining orthonormal bases
-- statement:
--   Let $d\ge2$ and $0\le x\le1$, and let $D_x$ be the $d$-dimensional channel replacing the input by $I/d$ with probability $x$. Its one-shot capacity $C_1$ optimizes the classical mutual information over finite ensembles of normalized input density matrices and finite output POVMs, without prior entanglement. Then
--
--   $$C_1(D_x)=\log_2d-H_d\!\left(1-x\frac{d-1}{d}\right).$$
--
--   For every orthonormal basis, the uniform ensemble of its $d$ basis states and the projective measurement in that same basis attain the maximum. Here $H_d(p)=-p\log_2p-(1-p)\log_2((1-p)/(d-1))$ in bits. This is an accessible-information result and does not identify the asymptotic unassisted capacity.
-- source:
--   Entanglement-Assisted Classical Capacity of Noisy Quantum Channels, arXiv:quant-ph/9904023v5, PDF p. 2, Equation (1): one-shot accessible capacity and attaining orthonormal bases

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P21

set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.Elementwise

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Gap48.P21

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Reuse the finite Pi-space extended norm explicitly. Matrix has the same
-- product topology, but the generic instance search did not bridge the alias.

attribute [local instance] QAlgorithms.Papers.Independent.Gap48.P21.matrixContinuousENorm

open QAlgorithms.Papers.Independent.Dependency50.P45
  (resourceCapacity standardEbit DMC shannonCapacity blockProb)

open QAlgorithms.Papers.Independent.Claimed50.P43 (finiteWeyl chaotic)

open QAlgorithms.Papers.Independent.Information100.P58 (singleErasure)

open QAlgorithms.Papers.Independent.Information100.P27 (qubitDephasing)

-- CE uses resourceCapacity standardEbit directly; C uses the same accepted
-- operational capacity with the one-dimensional product resource.

open QAlgorithms.Papers.Independent.Information100.P80 (quantumCapacity)

open QAlgorithms.Papers.Independent.Frontier30.P12 (IsStochastic)

/-- PDF p.2, Eq.(1): C1 and the attaining uniform ensemble in ANY orthonormal
basis, measured in that same basis. The objective is accessible information. -/
theorem depolarizingOneShot (d : ℕ) (hd : 2 ≤ d) (x : ℝ)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    let N := QuditFidelity.depolarizingMap d (by omega) x
    oneShotCapacity N = Real.logb 2 d - symmetricEntropy d (1-x*(d-1:ℕ)/d) ∧
    ∀ U : Matrix.unitaryGroup (Fin d) ℂ,
      IsGreatest (accessibleValues N) (basisInformation N U) ∧
      basisInformation N U = oneShotCapacity N := by sorry

end QAlgorithms.Papers.Independent.Gap48.P21

end
