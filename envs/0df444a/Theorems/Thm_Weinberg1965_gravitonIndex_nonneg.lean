-- Prove2me | Theorems.Thm_Weinberg1965_gravitonIndex_nonneg
-- name    : Weinberg1965.gravitonIndex_nonneg
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T23:05:35.116071+00:00
-- url     : https://prove2.me/theorems/8b6d97c9-02dc-4d4a-970a-a0a6ba340468
-- title:
--   Eq. (2.24) — the infrared-graviton exponent $B$ is nonnegative
-- statement:
--   Let $G>0$ and let the external lines $n$ have masses $m_n>0$, three-momenta $\mathbf p_n$ and signs $\eta_n=\pm1$, and assume energy–momentum conservation
--   $$\sum_n\eta_n\mathbf p_n=\mathbf 0,\qquad\sum_n\eta_nE_n=0.$$
--   Then the infrared-graviton exponent (2.24) satisfies
--   $$B=\int d^2\Omega\,B(\hat q)\ \ge\ 0.$$
--
--   The paper calls $B$ “the positive dimensionless constant”; its sign gives the vanishing of the virtual-graviton factor $(\lambda/\Lambda)^B$ in (2.27) as $\lambda\to0$ (“all processes have zero rate in the limit $\lambda\to0$”), later cancelled by real emission in (2.52).
--
--   **Formalization Note** Only $B\ge0$ is asserted: $B=0$ occurs in degenerate configurations (e.g. every incoming line matched by an identical outgoing line), so strict positivity needs extra hypotheses. Energy–momentum conservation is a standing assumption of the paper (it is used explicitly before Eq. (2.41)); without it the expression (2.24)–(2.25) can be negative.
-- source:
--   S. Weinberg, Infrared Photons and Gravitons, Phys. Rev. 140, B516 (1965), https://doi.org/10.1103/PhysRev.140.B516, p. B519, Eqs. (2.23)–(2.25); energy–momentum conservation as used on p. B520 before Eq. (2.41)

import Definitions.Def_Weinberg1965_Defs

namespace Weinberg1965

theorem gravitonIndex_nonneg {ι : Type*} [Fintype ι]
    (G : ℝ) (m : ι → ℝ) (p : ι → Vec3) (η : ι → ℝ)
    (hG : 0 < G) (hm : ∀ n, 0 < m n) (hη : ∀ n, η n = 1 ∨ η n = -1)
    (hmom : ∑ n, η n • p n = 0)
    (henergy : ∑ n, η n * energy (m n) (p n) = 0) :
    0 ≤ gravitonIndex G m p η := by
  sorry

end Weinberg1965
