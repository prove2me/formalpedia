-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_theorem30
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.theorem30
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:53:09.695511+00:00
-- url     : https://prove2.me/theorems/eef77d48-b96e-428a-b1e9-feb2344a674a
-- title:
--   Theorem 30: exact primal SDP value
-- statement:
--   For $N\ge1$ ports of local dimension $d\ge1$, let $\mathcal Y_N^{(d)}$ be the Young diagrams of $N$ boxes and height at most $d$. The physical teleportation matrix $M_N^{(d)}$ has diagonal equal to the number of removable corners and off-diagonal entry one exactly for distinct shapes related by a single-box move; all other entries vanish. Write $\lambda_{\max}$ for its largest eigenvalue and $F_{\mathrm{opt}}(N,d)$ for the maximum entanglement fidelity over the resource and Alice's measurement. Bob retains the named port and makes no unitary correction.
--
--   For $N\ge1$ and $d\ge1$, put $\sigma_a=d^{-N}V^{t_C}(a,C)$ on Alice's $N$ registers and input register $C$. Here $|\Phi^+\rangle=d^{-1/2}\sum_j|jj\rangle$, so $\sigma_a=d^{-(N-1)}I_{\bar a}\otimes|\Phi^+\rangle\langle\Phi^+|_{aC}$. Effective effects have entanglement fidelity $F(E)=d^{-2}\sum_a\operatorname{Tr}(E_a\sigma_a)$. They are distinct from physical effects summing to identity.
--
--   Over all positive semidefinite $X$ and effective effects $E_a\succeq0$ satisfying $\operatorname{Tr}X=d^N$ and $\sum_aE_a\preceq X\otimes I_C$, the maximum is attained and equals
--
--   $$\max_{X,E}F(E)=\frac{\lambda_{\max}(M_N^{(d)})}{d^2}.$$
--
--   No block-form assumption restricts the primal variables. This is an attained greatest value, not merely a supremum.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 16, Theorem 30: exact primal SDP value

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

/-- Theorem 30, unrestricted primal SDP with an attained greatest value
(PDF pp.16–19). No block ansatz or spectral identity is a hypothesis. -/
theorem theorem30 {d K : ℕ} (hd : 0 < d) :
    IsGreatest (primalValues d K) (spectralFidelity d (K+1)) ∧
    pbtOptimalFidelity d (K+1) = spectralFidelity d (K+1) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
