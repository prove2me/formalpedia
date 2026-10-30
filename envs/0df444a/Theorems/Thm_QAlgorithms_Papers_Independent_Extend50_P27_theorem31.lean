-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_theorem31
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.theorem31
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:53:54.16035+00:00
-- url     : https://prove2.me/theorems/2fbb7a60-d682-4648-8d1c-3e4fa0caf427
-- title:
--   Theorem 31: exact dual SDP value
-- statement:
--   For $N\ge1$ ports of local dimension $d\ge1$, let $\mathcal Y_N^{(d)}$ be the Young diagrams of $N$ boxes and height at most $d$. The physical teleportation matrix $M_N^{(d)}$ has diagonal equal to the number of removable corners and off-diagonal entry one exactly for distinct shapes related by a single-box move; all other entries vanish. Write $\lambda_{\max}$ for its largest eigenvalue and $F_{\mathrm{opt}}(N,d)$ for the maximum entanglement fidelity over the resource and Alice's measurement. Bob retains the named port and makes no unitary correction.
--
--   For $N\ge1$ and $d\ge1$, put $\sigma_a=d^{-N}V^{t_C}(a,C)$ on Alice's $N$ registers and input register $C$. Here $|\Phi^+\rangle=d^{-1/2}\sum_j|jj\rangle$, so $\sigma_a=d^{-(N-1)}I_{\bar a}\otimes|\Phi^+\rangle\langle\Phi^+|_{aC}$. Effective effects have entanglement fidelity $F(E)=d^{-2}\sum_a\operatorname{Tr}(E_a\sigma_a)$. They are distinct from physical effects summing to identity.
--
--   Over all Hermitian $\Omega$ on Alice and $C$ with $\Omega-\sigma_a\succeq0$ for every port, the dual minimum is attained and
--
--   $$\min_\Omega\frac{d^N}{d^2}\,\|\operatorname{Tr}_C\Omega\|_{\mathrm{op}}=\frac{\lambda_{\max}(M_N^{(d)})}{d^2}.$$
--
--   The partial trace is positive and Hermitian, so its Euclidean operator norm is its largest real eigenvalue. Complex entries are retained. No block ansatz is assumed.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 19, Theorem 31: exact dual SDP value

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

/-- Theorem 31, unrestricted Hermitian dual SDP with an attained least value
(PDF pp.19–21). The partial trace is over C, and its complex entries are retained. -/
theorem theorem31 {d K : ℕ} (hd : 0 < d) :
    IsLeast (pbtDualValues d K) (spectralFidelity d (K+1)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
