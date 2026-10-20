-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_zetaStrongConverse
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.zetaStrongConverse
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:41:21.060908+00:00
-- url     : https://prove2.me/theorems/afed3b1c-bdd7-4587-8056-71483ff05b63
-- title:
--   Theorem 12: ζ strong converse bound
-- statement:
--   Let $\mathcal N:A\to B$ be a CPTP channel on nonzero finite registers. Define $\zeta(\mathcal N)$ by the attained minimum of $\operatorname{Tr}S_B$ over Hermitian $V,S_B$ satisfying
--
--   $$V\succeq J_\mathcal N,\qquad-I_A\otimes S_B\preceq V^{T_B}\preceq I_A\otimes S_B.$$
--
--   Then
--
--   $$C(\mathcal N)\le C_{\mathrm{NS}\cap\mathrm{PPT}}(\mathcal N)\le C_\zeta(\mathcal N):=\log_2\zeta(\mathcal N).$$
--
--   For every $r>C_\zeta(\mathcal N)$ there exist $c>0,n_0\ge1$ such that for every $n\ge n_0$ and integer $M\ge1$ with $\log_2M\ge nr$, optimal NS∩PPT success on $\mathcal N^{\otimes n}$ is at most $2^{-cn}$. This is the second SDP strong converse for parallel memoryless uses.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 16, Theorem 12

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

/-- PDF pp.16–17, Theorem 12: the V^{T_B} constraints and exponential converse
hold for every physical integer message number above the given rate. -/
theorem zetaStrongConverse [Nonempty A] [Nonempty B] (N : Superop A B) (hN : IsChannel N) :
    IsLeast (zetaPlusValues N 1) (channelZeta N) ∧
    ordinaryClassicalCapacity N ≤ nsCapacity true N ∧ nsCapacity true N ≤ cZeta N ∧
    ExponentialConverse N (cZeta N) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
