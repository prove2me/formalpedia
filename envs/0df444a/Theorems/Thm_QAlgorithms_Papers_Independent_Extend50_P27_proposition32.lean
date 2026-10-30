-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P27_proposition32
-- name    : QAlgorithms.Papers.Independent.Extend50.P27.proposition32
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:54:37.464548+00:00
-- url     : https://prove2.me/theorems/431f4176-6395-402f-b7c4-458d24e52c8e
-- title:
--   Proposition 32: exact optimum, optimal effects and resource
-- statement:
--   For $N\ge1$ ports of local dimension $d\ge1$, let $\mathcal Y_N^{(d)}$ be the Young diagrams of $N$ boxes and height at most $d$. The physical teleportation matrix $M_N^{(d)}$ has diagonal equal to the number of removable corners and off-diagonal entry one exactly for distinct shapes related by a single-box move; all other entries vanish. Write $\lambda_{\max}$ for its largest eigenvalue and $F_{\mathrm{opt}}(N,d)$ for the maximum entanglement fidelity over the resource and Alice's measurement. Bob retains the named port and makes no unitary correction.
--
--   Choose a strictly positive vector $v$ with $\sum_\mu v_\mu^2=1$ and $M_N^{(d)}v=\lambda_{\max}v$. Then
--
--   $$
--   F_{\mathrm{opt}}(N,d)=\frac{\lambda_{\max}(M_N^{(d)})}{d^2},\qquad
--   \Pi=\frac{d^N}{\sqrt N}\sum_{\alpha}\sum_{\mu\in\alpha}\sqrt{\frac{m_\alpha}{d_\alpha}}\frac{v_\mu}{m_\mu}F_\mu(\alpha),\qquad
--   O_A=\sqrt{d^N}\sum_\mu\frac{v_\mu}{\sqrt{d_\mu m_\mu}}P_\mu.
--   $$
--
--   Here $P_\mu$ is the central tensor-permutation projector, $d_\mu$ its Specht dimension, $m_\mu$ its tensor multiplicity, and $F_\mu(\alpha)$ is the concrete Eq. (145) projector; sums range over compatible diagrams of heights at most $d$. The effective effects are $E_a=\Pi\sigma_a\Pi$, and the normalized resource is $|\Psi\rangle=(O_A\otimes I)|\Phi^+\rangle^{\otimes N}$. Inverse filtering on the support of $O_A$, followed by positive residual completion, gives an identity-summing physical POVM attaining this value. Every normalized resource filter and physical POVM has fidelity at most this value.
--
--   This gives both the attained maximum and an explicit optimal protocol.
-- source:
--   Optimal Port-based Teleportation, arXiv:1707.08456v1, PDF p. 21, Proposition 32: exact optimum, optimal effects and resource

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

/-- Proposition 32, all three bullets: value and the concrete effects/resource of
Eqs.(96)–(99), including normalization and physical deterministic completion
(PDF pp.21–22). Effective effects are not identified with identity-summing POVMs. -/
theorem proposition32 {d K : ℕ} (hd : 0 < d) :
    (∃ v : Partition d (K+1) → ℝ, IsOptimalVector v) ∧
    (∀ v : Partition d (K+1) → ℝ, IsOptimalVector v → OptimalConstruction v) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P27

end
