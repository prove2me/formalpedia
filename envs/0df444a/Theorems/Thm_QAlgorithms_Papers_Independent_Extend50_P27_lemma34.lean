-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_lemma34
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.lemma34
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:58:30.902955+00:00
-- url     : https://prove2.me/theorems/fe8e6a12-1bf5-45c1-8665-ba2feec4b728
-- title:
--   Lemma 34: fidelity of the blockwise power-filter measurement
-- statement:
--   Use $N\ge1$, $d\ge2$, physical diagrams $\alpha\vdash N-1$, $\mu\vdash N$, and one-box compatibility $\mu\in\alpha$. Let $d_\lambda$ and $m_\lambda$ be the actual Specht dimensions and tensor-permutation multiplicities. The operators $F_\mu(\alpha)$ are constructed by Eq. (145), and $\lambda_\mu(\alpha)=N m_\mu d_\alpha/(d^N m_\alpha d_\mu)>0$. All sums below use compatible physical labels. Write $\rho_\alpha^t=\sum_{\mu\in\alpha}\lambda_\mu(\alpha)^tF_\mu(\alpha)$, extended by zero off its support.
--
--   For $N\ge1$ and $d\ge1$, put $\sigma_a=d^{-N}V^{t_C}(a,C)$ on Alice's $N$ registers and input register $C$. Here $|\Phi^+\rangle=d^{-1/2}\sum_j|jj\rangle$, so $\sigma_a=d^{-(N-1)}I_{\bar a}\otimes|\Phi^+\rangle\langle\Phi^+|_{aC}$. Effective effects have entanglement fidelity $F(E)=d^{-2}\sum_a\operatorname{Tr}(E_a\sigma_a)$. They are distinct from physical effects summing to identity.
--
--   Let $z_\alpha\ge0$, $y_\alpha
--   e0$, and suppose the block power-filter effects $E_a=\sum_\alpha z_\alpha\rho_\alpha^{-1/y_\alpha}\sigma_a(\alpha)\rho_\alpha^{-1/y_\alpha}$ are feasible effective effects for some normalized resource variable. Then
--
--   $$F(E)=\frac1{d^{N+1}}\sum_\alpha z_\alpha c(\alpha,y_\alpha)\operatorname{Tr}\rho_\alpha^{1-1/y_\alpha},\qquad
--   c(\alpha,y)=\frac1d\sum_{\mu\in\alpha}\lambda_\mu(\alpha)^{-1/y}\frac{m_\mu}{m_\alpha}.$$
--
--   This computes the fidelity for this family and makes no assertion of optimality for arbitrary parameters.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 24, Lemma 34: fidelity of the blockwise power-filter measurement

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P27

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open Filter Topology

open QAlgorithms.Schur

namespace QAlgorithms.Papers.Independent.Extend50.P27

open QAlgorithms.Papers.Independent.Renew46.P26 (deleteLast)

open QAlgorithms.Papers.Independent.Gap20.P01 (spechtMatrix)

open QAlgorithms.Papers.Independent.Claimed50.P28 (traceInput)

attribute [local instance] Classical.propDecidable

/-- Lemma 34, Eqs.(112)–(113), for feasible effective measurements
(PDF pp.24–25). All powers are zero off support; y is nonzero, z nonnegative.
The source expressly disclaims optimality for arbitrary parameters. -/
theorem lemma34 {d K : ℕ} (hd : 2 ≤ d) (z y : Partition d K → ℝ)
    (hz : ∀ alpha, 0 ≤ z alpha) (hy : ∀ alpha, y alpha ≠ 0)
    (hfeasible : ∃ X, PBTPrimalFeasible X (powerEffects z y)) :
    effectFidelity (powerEffects z y) =
      (∑ alpha : Partition d K, z alpha * contractionConstant alpha (y alpha) *
        (blockPower alpha (1 - (y alpha)⁻¹)).trace.re) / (d : ℝ)^(K+2) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
