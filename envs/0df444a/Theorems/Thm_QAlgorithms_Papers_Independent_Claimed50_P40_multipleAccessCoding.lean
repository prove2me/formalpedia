-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P40_multipleAccessCoding
-- name    : QAlgorithms.Papers.Independent.Claimed50.P40.multipleAccessCoding
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T10:51:16.762749+00:00
-- url     : https://prove2.me/theorems/81b45346-2e33-45ec-a1f6-65aaf8095461
-- title:
--   Direct coding theorem for a fixed product input law
-- statement:
--   Let $W:X_1\times\cdots\times X_s\to\mathcal S(\mathcal Y)$ be a finite-dimensional memoryless channel with $s\ge1$ independent classical senders, finite nonempty alphabets, and one receiver with full output access. Fix any product law $P=\bigotimes_iP_i$, with channel state $\gamma_P$. Suppose $R_i\ge0$ and
--   $$
--   \sum_{i\in J}R_i\le I_{\gamma_P}(X(J):Y\mid X(J^c))\qquad(J\subseteq[s]).
--   $$
--   For every $\bar\epsilon,\delta>0$, there is $n_0\ge1$ such that every $n\ge n_0$ admits a fixed code with separate sender encoders, finite nonempty message sets $M_i$, and an arbitrary output-block POVM, satisfying
--   $$
--   \bar e\le\bar\epsilon,\qquad \frac{\log_2|M_i|}{n}\ge R_i-\delta\quad(i\in[s]).
--   $$
--   Error is averaged uniformly over the independent message tuple. Equality in any information constraint, zero rates, and zero probabilities in $P_i$ are permitted. This states operational achievability, with no circuit or running-time claim.
-- source:
--   The Capacity of the Quantum Multiple Access Channel, arXiv:quant-ph/9807019v3, PDF p. 4, Theorem 9

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P40

noncomputable section

open scoped BigOperators Matrix ComplexConjugate

namespace QAlgorithms.Papers.Independent.Claimed50.P40

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 9, PDF pp.4-5: all nonnegative rates in a fixed product-input polytope
are operationally achievable, including equality and zero-rate cases. The definition
requires an actual fixed code at every sufficiently large block length. -/
theorem multipleAccessCoding {s : ℕ} (C : ClassicalChannel s)
    (P : InputLaw C.alphabet) (R : Fin s → ℝ) (hR : R ∈ productLawRateRegion C P) :
    R ∈ capacityRegion (singleReceiver C) := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P40

end
