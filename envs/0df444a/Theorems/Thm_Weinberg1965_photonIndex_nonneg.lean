-- Prove2me | Theorems.Thm_Weinberg1965_photonIndex_nonneg
-- name    : Weinberg1965.photonIndex_nonneg
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-23T23:02:30.635359+00:00
-- url     : https://prove2.me/theorems/54aab6da-f703-4ca7-876c-db7afeca7629
-- title:
--   Eq. (2.14) — the infrared-photon exponent $A$ is nonnegative
-- statement:
--   Let the external lines $n$ have masses $m_n>0$, three-momenta $\mathbf p_n$, charges $e_n$ and signs $\eta_n=\pm1$, and assume charge conservation
--   $$\sum_n\eta_ne_n=0.$$
--   Then the infrared-photon exponent (2.14) satisfies
--   $$A=\int d^2\Omega\,A(\hat q)\ \ge\ 0.$$
--
--   The paper calls $A$ “the positive dimensionless constant”; its sign is what makes the virtual-photon factor $(\lambda/\Lambda)^A$ in (2.18) vanish as $\lambda\to0$ and the real-emission factor $(E/\lambda)^A$ in (2.48) blow up, so that the two cancel in (2.51).
--
--   **Formalization Note** Only $A\ge0$ is asserted: $A=0$ does occur in degenerate configurations (e.g. when every incoming line is matched by an outgoing line with the same mass, charge and momentum), so strict positivity is not true without further hypotheses. Charge conservation is a standing assumption of the paper (used explicitly around Eq. (2.39)); without it $A$ can be negative (e.g. a single line).
-- source:
--   S. Weinberg, Infrared Photons and Gravitons, Phys. Rev. 140, B516 (1965), https://doi.org/10.1103/PhysRev.140.B516, p. B518, Eqs. (2.14)–(2.15); charge conservation as used on p. B520 before Eq. (2.39)

import Definitions.Def_Weinberg1965_Defs

namespace Weinberg1965

theorem photonIndex_nonneg {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (p : ι → Vec3) (e η : ι → ℝ)
    (hm : ∀ n, 0 < m n) (hη : ∀ n, η n = 1 ∨ η n = -1)
    (hcharge : ∑ n, η n * e n = 0) :
    0 ≤ photonIndex m p e η := by
  sorry

end Weinberg1965
