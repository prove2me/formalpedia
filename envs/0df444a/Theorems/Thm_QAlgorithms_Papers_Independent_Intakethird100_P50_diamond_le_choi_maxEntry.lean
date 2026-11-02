-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Intakethird100_P50_diamond_le_choi_maxEntry
-- name    : QAlgorithms.Papers.Independent.Intakethird100.P50.diamond_le_choi_maxEntry
-- status  : Open
-- author  : @Gohan
-- created : 2026-11-01T06:51:12.4028+00:00
-- url     : https://prove2.me/theorems/6632b64c-ace9-4763-b19f-c7aeaa9e81f6
-- title:
--   Lemma 1: diamond norm bounded by Choi entrywise norm
-- statement:
--   Let $A,B$ be nonzero finite-dimensional complex Hilbert spaces with fixed orthonormal bases and let $\Theta:\mathcal B(A)\to\mathcal B(B)$ be any complex-linear map. Define its unnormalized reference-first Choi matrix by $J(\Theta)_{(i,b),(j,c)}=\Theta(|i\rangle\langle j|)_{b,c}$ and write $\|J\|_{\max}=\max_{u,v}|J_{u,v}|$. Then
--   $$
--   \|\Theta\|_\diamond\le (\dim A)(\dim B)^2\|J(\Theta)\|_{\max}.
--   $$
--   Here the diamond norm is the stabilized induced trace norm on all operators; positivity and trace preservation are not assumed. This converts entrywise Choi estimates into channel-norm estimates.
-- source:
--   Quantum and private capacities of low-noise channels, arXiv:1705.04335v3, PDF p. 5, Lemma 1: diamond norm bounded by Choi entrywise norm

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P50

noncomputable section

open scoped BigOperators Matrix ComplexConjugate ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Intakethird100.P50

variable {A B E F : Type}

variable [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

variable [Fintype E] [DecidableEq E] [Fintype F] [DecidableEq F]

open QAlgorithms.Papers.Independent.Information100.P67
  (IsIsometry receiverChannel complementaryChannel maximumCoherentInformation
    dilationPower idealJoint)

open QAlgorithms.Papers.Independent.Information100.P80 (log2)

open QAlgorithms.Papers.Independent.Information100.P69 (diamond choi)

open QAlgorithms.Papers.Independent.Support50.P07 (fullTracePrivateCapacity)

open QAlgorithms.Papers.Independent.Frontier18.P17 (clock)

/-- Lemma 1, PDF p.5: arbitrary complex-linear maps, without CP, TP or Hermiticity
assumptions. The Choi matrix is unnormalized and reference-first. -/
theorem diamond_le_choi_maxEntry [Nonempty A] [Nonempty B]
    (Theta : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ) :
    diamond Theta ≤ (Fintype.card A : ℝ) * (Fintype.card B : ℝ) ^ 2 *
      maxEntry (choi Theta) := by sorry

end QAlgorithms.Papers.Independent.Intakethird100.P50

end
