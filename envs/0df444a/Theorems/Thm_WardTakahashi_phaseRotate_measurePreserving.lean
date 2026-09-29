-- Prove2me | Theorems.Thm_WardTakahashi_phaseRotate_measurePreserving
-- name    : WardTakahashi.phaseRotate_measurePreserving
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-27T20:42:08.597973+00:00
-- url     : https://prove2.me/theorems/a99f5468-6d00-4a9b-a553-7783c1148442
-- title:
--   Invariance of the lattice measure under global $U(1)$ rotations
-- statement:
--   Let $N\ge0$ and $\theta\in\mathbb R$. The global phase rotation $R_\theta:\mathbb C^N\to\mathbb C^N$, $(R_\theta\varphi)_y=e^{i\theta}\varphi_y$, preserves Lebesgue measure $d\varphi$ on $\mathbb C^N\cong\mathbb R^{2N}$:
--   $$(R_\theta)_*\,d\varphi=d\varphi .$$
--
--   This is the finite-dimensional counterpart of the invariance of the functional measure $\mathcal D\varphi$ under the symmetry, the starting point of the path-integral derivation of the Ward–Takahashi identities.
-- source:
--   Wikipedia, "Ward–Takahashi identity" (revision oldid=1374751657), https://en.wikipedia.org/w/index.php?title=Ward%E2%80%93Takahashi_identity&oldid=1374751657 ; section "Derivation in the path integral formulation" (finite-dimensional lattice model)

import Mathlib
import Definitions.Def_WardTakahashi_LatticeU1

open MeasureTheory Complex

namespace WardTakahashi

theorem phaseRotate_measurePreserving {N : ℕ} (θ : ℝ) :
    MeasurePreserving (phaseRotate (N := N) θ) volume volume := by sorry

end WardTakahashi
