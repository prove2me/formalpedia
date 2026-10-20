-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P23_cqReduction
-- name    : QAlgorithms.Papers.Independent.Dependency50.P23.cqReduction
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T16:37:20.320886+00:00
-- url     : https://prove2.me/theorems/5794ee8c-2e95-4870-ab89-783f54166971
-- title:
--   Proposition 8: cq-channel SDP reduction
-- statement:
--   Let $A,B$ be nonzero finite complex registers, and let $\rho_x$ be a density matrix on $B$ for every basis label $x\in A$. The cq channel dephases the input and sends $x$ to $\rho_x$; its unnormalized Choi matrix is $J_\mathcal N=\sum_x|x\rangle\langle x|\otimes\rho_x$. For $0\le e<1$,
--
--   $$C_{\mathrm{NS}}^{(1)}(\mathcal N,e)=C_{\mathrm{NS}\cap\mathrm{PPT}}^{(1)}(\mathcal N,e)=\log_2\max\sum_xs_x,$$
--
--   where $0\preceq Q_x\preceq s_xI_B$, $\sum_xQ_x=I_B$, and $\sum_x\operatorname{Tr}(Q_x\rho_x)\ge(1-e)\sum_xs_x$. The maximum is attained. These continuous one-shot capacities therefore agree on all cq channels, and admit a smaller SDP.
-- source:
--   Semidefinite programming strong converse bounds for classical capacity, arXiv:1610.06381v4, PDF p. 12, Proposition 8

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

/-- PDF pp.12–13, Proposition 8: exact cq choi formula, equality of the two
continuous capacities, and the attained maximum of the reduced SDP. -/
theorem cqReduction [Nonempty A] [Nonempty B] (rho : A → Matrix B B ℂ)
    (hrho : ∀ x, IsDensityMatrix (rho x)) (e : ℝ) (he0 : 0 ≤ e) (he1 : e < 1) :
    choi (cqChannel rho) =
      ∑ x, Matrix.kronecker (Matrix.single x x 1) (rho x) ∧
    oneShot false (cqChannel rho) e = oneShot true (cqChannel rho) e ∧
    oneShot false (cqChannel rho) e = log2 (sSup (cqValues rho e)) ∧
    IsGreatest (cqValues rho e) (sSup (cqValues rho e)) := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P23

end
