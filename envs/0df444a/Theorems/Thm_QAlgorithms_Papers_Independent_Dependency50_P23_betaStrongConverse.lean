-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_betaStrongConverse
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.betaStrongConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:39:28.899453+00:00
-- url     : https://prove2.me/theorems/2773c23a-8a52-4765-ae63-bda5d0d70776
-- title:
--   Theorem 11: β strong converse bound (original seed pinned from abstract)
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on nonzero finite registers. Its Choi matrix $J_\mathcal N$ is unnormalized and input first. Let $\beta(\mathcal N)$ be the attained minimum of $\operatorname{Tr}S_B$ over Hermitian $R,S_B$ satisfying
--
--   $$-R\preceq J_\mathcal N^{T_B}\preceq R,\qquad-I_A\otimes S_B\preceq R^{T_B}\preceq I_A\otimes S_B.$$
--
--   With $d_B=\dim B$ and spectral operator norm $\|\cdot\|_\infty$,
--
--   $$C(\mathcal N)\le C_{\mathrm{NS}\cap\mathrm{PPT}}(\mathcal N)\le C_\beta(\mathcal N):=\log_2\beta(\mathcal N)\le\log_2(d_B\|J_\mathcal N^{T_B}\|_\infty).$$
--
--   For every $r>C_\beta(\mathcal N)$ there exist $c>0$ and $n_0\ge1$ such that, for all $n\ge n_0$ and integers $M\ge1$ with $\log_2M\ge nr$, optimal NS∩PPT success over $\mathcal N^{\otimes n}$ is at most $2^{-cn}$. Constants precede blocklength, messages and codes. This is a strong converse without feedback.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 16, Theorem 11

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

/-- PDF pp.1,16, Theorem 11: actual beta SDP, full capacity chain, the upper
spectral norm of J^{T_B}, and uniform exponential strong converse. -/
theorem betaStrongConverse [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) :
    IsLeast (plusValues N 1) (channelBeta N) ∧
    ordinaryClassicalCapacity N ≤ nsCapacity true N ∧ nsCapacity true N ≤ cBeta N ∧
    cBeta N ≤ log2 ((Fintype.card B : ℝ) * specNorm (PT (choi N))) ∧
    ExponentialConverse N (cBeta N) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
