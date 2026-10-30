-- Prove2me | Theorems.Thm_QAlgorithms_Papers_Independent_Extend50_P20_deterministic_optimal_fidelity
-- name    : QAlgorithms.Papers.Independent.Extend50.P20.deterministic_optimal_fidelity
-- status  : Open
-- author  : @Gohan
-- created : 2026-10-29T20:07:26.314718+00:00
-- url     : https://prove2.me/theorems/0408c769-8ef2-4273-a6a1-9ce60a25984f
-- title:
--   Optimal deterministic fidelity and the teleportation matrix
-- statement:
--   Let $d\ge1$ and $1\le k\le N$. For height-at-most-$d$ diagrams $\alpha\vdash N-k$ and $\mu\vdash N$, let $m_{\mu/\alpha}$ count all paths adding one box at a time from $\alpha$ to $\mu$ through valid Young diagrams, with count zero if no path exists. Define
--
--   $$M_{\mu\nu}=\sum_{\alpha\vdash N-k,\,h(\alpha)\le d}m_{\mu/\alpha}m_{\nu/\alpha}.$$
--
--   Optimize the deterministic ordered-port MPBT protocol jointly over normalized pure resources and Alice's measurements, with no correction beyond Bob's port selection and ordering. The maximum entanglement fidelity against the normalized maximally entangled $k$-qudit state is attained and equals
--
--   $$F_{\mathrm{opt}}=d^{-2k}\lambda_{\max}(M).$$
--
--   This reduces the optimum to a matrix determined by Young paths. **Formalization Note** The largest eigenvalue uses the unit-vector Rayleigh characterization. Definition 6's printed $S(N-1)$ is read as $S(N-k)$, following (83)–(85).
-- source:
--   Optimal Multi-port-based Teleportation Schemes, arXiv:2011.09256v3, PDF p. 13, Theorem 7 / Eq. (39)

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P20

noncomputable section

open scoped BigOperators Matrix ComplexOrder

open Filter

namespace QAlgorithms.Papers.Independent.Extend50.P20

attribute [local instance] Classical.propDecidable

/-- Theorem 7, PDF p.13, Eq.(39); Appendix B pp.19-21.
Definition 6's S(N-1) is read as S(N-k), following Eqs.(83)-(85).
The matrix and its spectrum are computed from actual legal Young paths. -/
theorem deterministic_optimal_fidelity (d N k : ℕ)
    (hd : 0 < d) (hk : 1 ≤ k) (hkN : k ≤ N) :
    IsGreatest (detValues d N k)
      (largestTeleportationEigenvalue d N k / (d : ℝ)^(2*k)) := by sorry

end QAlgorithms.Papers.Independent.Extend50.P20

end
