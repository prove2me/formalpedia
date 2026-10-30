-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P08_deterministic_resource_minimal_success
-- name    : QAlgorithms.Papers.Independent.Extend50.P08.deterministic_resource_minimal_success
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:26:08.251954+00:00
-- url     : https://prove2.me/theorems/df88795a-7068-402c-80be-f6c71f4012f3
-- title:
--   Success with the deterministic-optimal resource
-- statement:
--   Let $N\ge1$ and $d\ge2$. On height-bounded diagrams with $N$ boxes construct the teleportation matrix $M_{\mu\nu}=\sum_{\alpha\vdash N-1}\mathbf1_{\mu\in\alpha}\mathbf1_{\nu\in\alpha}$. Let $v$ be any real nonnegative unit principal eigenvector. For the actual Young isotypic projectors $P_\mu$, use the resource filter $\widetilde O=\sqrt{d^N}\sum_\mu v_\mu P_\mu/\sqrt{d_\mu m_\mu}$ and the same physical uncompleted SRM effects as in (18), together with their failure effect. This defines a physical protocol and
--
--   $$p_{\mathrm{succ}}=\frac1d\sum_{\alpha\vdash N-1}\sum_{\mu\in\alpha}\frac{m_\alpha}{m_\mu}v_\mu^2.$$
--
--   This is a success evaluation for the deterministic-optimal resource, with no scalar optimality claim for minimal PBT. Here $d_\lambda$ is the dimension of the actual symmetric-group Specht module labelled by $\lambda$, and $m_\lambda$ is its Schur–Weyl multiplicity for local dimension $d$ (with $d=2$ in the qubit case).
-- source:
--   Minimal Port-based Teleportation, arXiv:2111.05499v2, PDF p. 9, Theorem 3: mPBT success with the deterministic-optimal resource

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P08

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Matrix.Norms.L2Operator

namespace QAlgorithms.Papers.Independent.Extend50.P08

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Theorem 3, PDF pp.9–10, Eqs.(30)–(34): the deterministic-optimal resource
is computed from every allowed principal vector; no optimal mPBT objective is claimed. -/
theorem deterministic_resource_minimal_success (d N : ℕ) (hd : 2 ≤ d) (hN : 0 < N)
    (v : Schur.Partition d N → ℝ) (hv : IsPrincipal v) :
    IsPhysicalPBT (deterministicFilter v) (minimalEffects d N) ∧
    pbtSuccess (deterministicFilter v) (minimalEffects d N) = optimizedSuccessFormula v := by sorry

end QAlgorithms.Papers.Independent.Extend50.P08

end
