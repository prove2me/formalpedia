-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Frontier30_P12_oneWaySecretKey
-- name    : QAlgorithms.Papers.Independent.Frontier30.P12.oneWaySecretKey
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T17:04:12.268058+00:00
-- url     : https://prove2.me/theorems/07672428-cbfc-44e0-a5e8-de5d800e5f6a
-- title:
--   Theorem 1: one-way secret-key coding theorem
-- statement:
--   Let $\mathcal X$ be a finite nonempty alphabet, let $B,E$ be finite complex registers of positive dimension, let $P$ be a probability law, and let $\rho_x^{BE}$ be normalized density operators. Write $\rho^{ABE}=\sum_xP(x)|x\rangle\langle x|\otimes\rho_x^{BE}$, and let $I(X;B)$ and $I(X;E)$ be its Holevo informations in bits. Then
--
--   $$K_{\to}(\rho)\ge I(X;B)-I(X;E).$$
--
--   Here $K_{\to}$ is the supremum of operational rates obtained from independent copies by Alice's stochastic encoder and Bob's transcript-dependent POVM. The same authenticated public transcript is received by Eve. For a protocol sequence there is one finite $F$ with $L_n\le2^{nF}$ for every $n$. The key disagreement probability, full $\ell_1$ nonuniformity, and full trace norm distance of every key-conditional transcript/Eve state from one common normalized state all tend to zero. The rate is the limit of $\log_2 M_n/n$, with protocols for every block length.
--
--   This is the one-way coding lower bound. Eve need not purify $AB$; a negative information difference asserts no negative achievable rate.
-- source:
--   Distillation of secret key and entanglement from quantum states, arXiv:quant-ph/0306078v1, PDF p. 2, Theorem 1

import Definitions.Def_QAlgorithms_Papers_Independent_Frontier30_P12

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

namespace QAlgorithms.Papers.Independent.Frontier30.P12

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P21 (Op Vec)

open QAlgorithms.Papers.Independent.Information100.P56 (IsLaw)

open QAlgorithms.Papers.Independent.Information100.P27 (shannon labelInformation)

open QAlgorithms.Papers.Independent.Dependency50.P21 (marginalAB)

/-- arXiv:quant-ph/0306078v1, PDF p.2, Theorem 1 (seed announced on p.1).
Eve is arbitrary, and the lower bound may be nonpositive. -/
theorem oneWaySecretKey {X B E : Type} [Fintype X] [Fintype B] [Fintype E]
    [Nonempty X] [Nonempty B] [Nonempty E]
    (p : X → ℝ) (W : X → Op (B × E)) (h : IsCqq p W) :
    cqqAdvantage p W ≤ cqqKeyCapacity p W := by sorry

end QAlgorithms.Papers.Independent.Frontier30.P12

end
