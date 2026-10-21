-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Claimed50_P01_algorithm1_correct
-- name    : QAlgorithms.Papers.Independent.Claimed50.P01.algorithm1_correct
-- status  : Open
-- author  : @Goku
-- created : 2026-10-20T08:28:42.177964+00:00
-- url     : https://prove2.me/theorems/70790717-1d75-413e-89e7-52d032766f87
-- title:
--   Algorithm 1 has exactly the weak Schur sampling final-label marginal
-- statement:
--   Let $d\ge2$ and $n\ge1$. Fix the one-qudit Clebsch–Gordan unitary intertwiners independently of the input, use the same maps on all multiplicity copies, and let $\rho$ be any positive semidefinite trace-one operator on $(\mathbb C^d)^{\otimes n}$. A valid path $p$ starts at the one-box shape and adds one box per arrival; its subnormalized branch is $K_p\rho K_p^\dagger$, with $K_p$ the time-ordered product of the measured CG blocks, tensored with identities on unread systems.
--
--   If $\Lambda$ is the final Young label of this sequential protocol, then for every nonincreasing $d$-row Young label $\lambda$ of size $n$,
--
--   $$
--   \Pr[\Lambda=\lambda]
--   =\sum_{p:\,p_n=\lambda}\operatorname{Tr}(K_p\rho K_p^\dagger)
--   =\operatorname{Tr}(\rho\Pi_\lambda^{\mathrm{Std}}).
--   $$
--
--   Here $\Pi_\lambda^{\mathrm{Std}}$ is the full isotypic projector, including all multiplicity copies. This is exact weak Schur sampling, with no independence assumption on the successive input systems. The trace expression is real because the input is a density operator and the target is an orthogonal projector.
-- source:
--   Weak Schur sampling with logarithmic quantum memory, arXiv:2309.11947v1, PDF p. 6, Theorem 1, Eq.(18)

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P01

noncomputable section

open scoped Matrix

namespace QAlgorithms.Papers.Independent.Claimed50.P01

attribute [local instance] Classical.propDecidable

/-- Theorem 1, Eq.(18): Algorithm 1's final-label marginal on every density
operator, with no iid or product-state hypothesis (PDF p.6; proof pp.7-9).
The local CG coordinates are fixed before rho. -/
theorem algorithm1_correct {d n : ℕ} (hd : 2 ≤ d) (hn : 1 ≤ n)
    (C : CGSystem d) (rho : Matrix ((Fin n → Fin d)) ((Fin n → Fin d)) ℂ)
    (hrho : IsDensityMatrix rho) (lambda : Schur.Partition d n) :
    labelProbability C lambda rho = effectProb (Schur.weakSampling d n lambda) rho := by sorry

end QAlgorithms.Papers.Independent.Claimed50.P01

end
