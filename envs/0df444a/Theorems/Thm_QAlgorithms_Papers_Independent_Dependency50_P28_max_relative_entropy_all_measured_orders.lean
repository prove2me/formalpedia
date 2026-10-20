-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P28_max_relative_entropy_all_measured_orders
-- name    : QAlgorithms.Papers.Independent.Dependency50.P28.max_relative_entropy_all_measured_orders
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T18:10:27.065695+00:00
-- url     : https://prove2.me/theorems/6a5ad41a-14bc-4d73-897a-8b3a0cd63e10
-- title:
--   Dmax is the largest measured classical Renyi divergence at any order
-- statement:
--   For density operators ρ,σ, take all finite POVMs M and all classical Renyi orders α∈[0,∞], including the standard classical endpoint limits. Their largest measured value is Dmax(ρ‖σ):
--
--   Here $D(\rho\Vert\sigma)=\operatorname{Tr}[\rho(\log\rho-\log\sigma)]/\operatorname{Tr}\rho$ on nested supports and $+\infty$ otherwise, and $D_{\max}(\rho\Vert\sigma)=\inf\{a\in\mathbb R:\rho\leq e^a\sigma\}$, with the empty infimum equal to $+\infty$. All operator inequalities are in Loewner order.
--
--   $$
--   D_{\max}(\rho\Vert\sigma)=\max_{\alpha\in[0,\infty]}\max_M D_\alpha(M(\rho)\Vert M(\sigma)).
--   $$
--
--   The statement characterizes max-relative entropy through all measured classical orders.
-- source:
--   Quantum hypothesis testing and the operational interpretation of the quantum Renyi relative entropies, arXiv:1309.3228v5, PDF p. 24, Remark A.7 It is easy to see that for fixed states, the classical Rényi relative entropies are monotone

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P28

noncomputable section

namespace QAlgorithms.Papers.Independent.Dependency50.P28

open scoped Matrix ComplexConjugate ComplexOrder BigOperators

open Filter QAlgorithms

open QAlgorithms.Papers.Independent.Information100.P60 (Mat copies)

open QAlgorithms.Papers.Independent.Information100.P07 (support positivePart positiveProjection)

open QAlgorithms.Papers.Independent.Information100.P71 (supportPower)

attribute [local instance] Classical.propDecidable Classical.decEq

variable {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- arXiv:1309.3228v5, PDF p.24: Dmax is the largest measured classical Renyi divergence at any order. IsGreatest asserts both an upper bound and actual attainment. A separate measurement attains the value at infinity, so the outer maximum is attained there. Classical zero order is defined; no quantum zero-order definition is invented. -/
theorem max_relative_entropy_all_measured_orders (rho sigma : Mat I) (hrho : IsDensityMatrix rho) (hsigma : IsDensityMatrix sigma) :
    IsGreatest (allMeasuredValues rho sigma) (Dmax rho sigma) ∧
    ∃ M : POVM I,
      classicalD ClassicalOrder.infinity ((fun x => effectProb (M.effect x) rho)) ((fun x => effectProb (M.effect x) sigma)) = Dmax rho sigma := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P28

end
