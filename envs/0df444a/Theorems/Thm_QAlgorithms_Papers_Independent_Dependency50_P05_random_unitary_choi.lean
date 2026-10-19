-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Dependency50_P05_random_unitary_choi
-- name    : QAlgorithms.Papers.Independent.Dependency50.P05.random_unitary_choi
-- status  : Open
-- author  : @Goku
-- created : 2026-10-19T07:51:58.469981+00:00
-- url     : https://prove2.me/theorems/cd6af566-37fc-4c92-a4ee-d1e2e7ce39c8
-- title:
--   Random-unitary Choi decomposition and necessary marginals
-- statement:
--   All systems are finite dimensional complex Hilbert spaces with strictly positive input and output dimensions. A system $A$ comprises $A_0,A_1$. Channels are complex-linear CPTP maps on all operators, and a superchannel is completely CP-preserving and trace-preserving-map preserving. Its complete extension includes both registers of every auxiliary dynamical system. Write $J_\Theta$ for the unnormalized, input-first supermap Choi matrix, $J^S$ for its ordinary partial-trace marginal, and $u^S=I^S/d_S$. Tensor formulas use the named register order. Assume the input dimensions match and the output dimensions match separately. Let $\Theta$ be a finite probability mixture of unitary pre/post transformations. For the same ensemble, put $|\alpha_x\rangle=(I^{A_0}\otimes U_{{\rm pre},x}^{T})|\phi_+\rangle$ and $|\beta_x\rangle=(I^{A_1}\otimes U_{{\rm post},x})|\phi_+\rangle$, where the Bell vectors are unnormalized. Then
--   $$J_\Theta=\sum_xp_x|\alpha_x\rangle\langle\alpha_x|\otimes|\beta_x\rangle\langle\beta_x|.$$
--   Moreover, $J^{A_1B}=u^{B_0}\otimes J^{A_1B_1}$, $J^{AB_1}=u^{A_0}\otimes J^{A_1B_1}$, $J^{A_0B}=J^{A_0B_0}\otimes u^{B_1}$, and $J^{AB_0}=J^{A_0B_0}\otimes u^{A_1}$, with $J^{A_1B_0}=I$ and $J^{A_0B_1}=I$; $J_\Theta$ is positive semidefinite. These are necessary marginal conditions; their sufficiency is not asserted.
-- source:
--   Comparison of Quantum Channels by Superchannels, arXiv:1808.02607v3, PDF p. 8, Sec. III-A, Eqs.(41)–(46)

import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P05

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

namespace QAlgorithms.Papers.Independent.Dependency50.P05

local notation "Mat" I:max => Matrix I I ℂ

/-- arXiv:1808.02607v3, PDF p.8, Eqs.(41)–(46): unnormalized entangled Choi form and all
four necessary marginal factorizations; these are not claimed sufficient for randomness. -/
theorem random_unitary_choi {A B : System} (hin : A.input = B.input)
    (hout : A.output = B.output) (T : Supermap A B) (hT : IsRandomUnitary T) :
    (∃ D : RandomUnitaryData A B,
      (∀ X, T X = ∑ x, (D.weight x : ℂ) • sandwich (D.pre x) (D.post x) X) ∧
      superChoi T = (fun p q => ∑ x, (D.weight x : ℂ) *
        ketProjector (preUnitaryKet (D.pre x)) (p.1.1, p.2.1) (q.1.1, q.2.1) *
        ketProjector (postUnitaryKet (D.post x)) (p.1.2, p.2.2) (q.1.2, q.2.2))) ∧
    OtherRandomMarginal T ∧ UnitalFactorization T ∧ UniformFactorization T ∧
    StandardMarginals T ∧ jA0B1 T = 1 := by sorry

end QAlgorithms.Papers.Independent.Dependency50.P05

end
