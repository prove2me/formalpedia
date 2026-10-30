-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P18_deterministic_entanglement_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P18.deterministic_entanglement_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T19:56:12.827011+00:00
-- url     : https://prove2.me/theorems/39f799bf-ab2e-48da-a608-c7a7058da1b5
-- title:
--   Theorem 22 / paper headline: deterministic MPBT entanglement fidelity
-- statement:
--   Let $d\ge1$, $k\ge1$, and $N\ge2k$ be integers. The shared resource is $N$ normalized maximally entangled qudit pairs. Alice uses the completed square-root measurement for the signals $\sigma_i=d^{-(N-k)}I_{\bar A_i}\otimes P^+_{A_iC}$ indexed by ordered injections $i:\{1,\ldots,k\}\hookrightarrow\{1,\ldots,N\}$. Bob retains the indicated ports in that order. Let $m_\mu$ and $d_\mu$ be the actual Schur–Weyl multiplicity and symmetric-group dimension of a height-at-most-$d$ partition $\mu$, and let $m_{\mu/\alpha}$ count saturated height-bounded Young paths from $\alpha$ to $\mu$. Then the entanglement fidelity is
--
--   $$
--   F=\frac1{d^{N+2k}}\sum_{\alpha\vdash_d N-k}\left(\sum_{\mu\vdash_d N}m_{\mu/\alpha}\sqrt{m_\mu d_\mu}\right)^2.
--   $$
--
--   Absent paths contribute zero. This gives the exact performance of this specified deterministic protocol.
--
--   **Formalization Note** The code writes $N=r+k$ and requires $k\le r$.
-- source:
--   Efficient multi port-based teleportation schemes, arXiv:2008.00984v4, PDF p. 18, Theorem 22 / paper headline

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P18

noncomputable section

open scoped BigOperators Matrix ComplexOrder

namespace QAlgorithms.Papers.Independent.Extend50.P18

attribute [local instance] Classical.propDecidable

/-- Theorem 22: exact deterministic SRM fidelity for N=r+k fixed Bell ports.
The paper's k>=1 and 2k<=N become k>=1 and k<=r. No optimality over other
POVMs or resource states is asserted (PDF pp.18-19, (134),(140)). -/
theorem deterministic_entanglement_fidelity (d r k : ℕ)
    (hd : 0 < d) (hk : 0 < k) (hports : k ≤ r) :
    protocolFidelity (d := d) (N := r+k) (k := k) srmEffect =
      fidelityExpression d r k := by sorry

end QAlgorithms.Papers.Independent.Extend50.P18

end
