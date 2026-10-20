-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_qutritOneBit
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.qutritOneBit
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:45:21.307518+00:00
-- url     : https://prove2.me/theorems/5c19f341-0480-43c1-9426-22cbadcc4796
-- title:
--   Proposition 15: one-bit qutrit-channel capacities
-- statement:
--   For $0<\alpha\le\pi/4$, define the qutrit channel $\mathcal N_\alpha(X)=E_0XE_0^\dagger+E_1XE_1^\dagger$, with $E_0=\sin\alpha|0\rangle\langle1|+|1\rangle\langle2|$ and $E_1=\cos\alpha|2\rangle\langle1|+|1\rangle\langle0|$. Then
--
--   $$C(\mathcal N_\alpha)=C_{\mathrm{NS}\cap\mathrm{PPT}}(\mathcal N_\alpha)=C_\beta(\mathcal N_\alpha)=1.$$
--
--   The capacities are operational asymptotic classical rates in bits per use; $C_\beta$ is the SDP bound. The channel is constructed from its Kraus operators, and distinguishability of useful inputs is a consequence rather than a premise.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 19, Proposition 15

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P23

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P23

open scoped Matrix ComplexConjugate ComplexOrder

open Filter

open QAlgorithms.Papers.Independent.Information100.P34 (choi)

open QAlgorithms.Papers.Independent.Information100.P08 (canonicalPurification)

open QAlgorithms.Papers.Independent.Information100.P62 (tensorChannel)

open QAlgorithms.Papers.Independent.Information100.P80 (log2 quantumCapacity)

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

variable {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]

variable [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]

/-- PDF p.19, Proposition 15: the constructed qutrit family's three capacities. -/
theorem qutritOneBit (alpha : ℝ) (ha0 : 0 < alpha) (ha1 : alpha ≤ Real.pi/4) :
    ordinaryClassicalCapacity (qutrit alpha) = 1 ∧
    nsCapacity true (qutrit alpha) = 1 ∧ cBeta (qutrit alpha) = 1 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
