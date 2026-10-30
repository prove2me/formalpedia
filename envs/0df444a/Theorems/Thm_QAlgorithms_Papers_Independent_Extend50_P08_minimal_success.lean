-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P08_minimal_success
-- name    : QAlgorithms.Papers.Independent.Extend50.P08.minimal_success
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:25:19.501238+00:00
-- url     : https://prove2.me/theorems/3c7008fa-669e-4757-8764-a4d62538fe36
-- title:
--   Nonoptimized minimal-PBT success probability
-- statement:
--   Fix $N\ge1$ ports of dimension $d\ge2$, the normalized Bell-pair resource, and the uncompleted square-root effects $\Pi_i=\rho^{-1/2}\sigma_i\rho^{-1/2}$, completed by the failure effect $\Delta$. Let $d_\mu$ be the dimension of the actual symmetric-group Specht module and $m_\alpha$ its Schur–Weyl multiplicity. Sums range over Young diagrams of height at most $d$; $\mu\in\alpha$ means one added box. The resulting family is a physical POVM, and its Choi-average success probability satisfies
--
--   $$p_{\mathrm{succ}}=\frac{1}{d^{N+1}}\sum_{\alpha\vdash N-1}\sum_{\mu\in\alpha}d_\mu m_\alpha.$$
--
--   For $d=2$ this is $1-(N+2)/2^{N+1}$. This evaluates the actual SRM protocol without assuming a support-rank identity.
-- source:
--   Minimal Port-based Teleportation, arXiv:2111.05499v2, PDF p. 7, Theorem 2: nonoptimized mPBT success probability

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P08

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P08

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 2, PDF pp.7–8, Eqs.(19),(20). No support-rank formula is assumed. -/
theorem minimal_success (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N) :
    IsPhysicalPBT (1 : AliceMatrix d N) (minimalEffects d N) ∧
    pbtSuccess (1 : AliceMatrix d N) (minimalEffects d N) = minimalSuccessFormula d N ∧
    (d = 2 → pbtSuccess (1 : AliceMatrix d N) (minimalEffects d N) =
      1 - ((N : ℝ) + 2) / 2 ^ (N + 1)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P08

end
