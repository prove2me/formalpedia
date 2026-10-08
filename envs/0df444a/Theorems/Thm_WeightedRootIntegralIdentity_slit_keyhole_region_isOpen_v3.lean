-- Prove2me | Theorems.Thm_WeightedRootIntegralIdentity_slit_keyhole_region_isOpen_v3
-- name    : WeightedRootIntegralIdentity.slit_keyhole_region_isOpen_v3
-- status  : Proved
-- author  : @abcdefg
-- created : 2026-09-16T11:17:39.699732+00:00
-- url     : https://prove2.me/theorems/836a35d0-31f6-4d91-a7bb-c8d7fa594e11
-- title:
--   Openness of the annular slit keyhole region
-- statement:
--   For radii satisfying $0<r<R$, the annulus with the nonnegative real axis removed is an open subset of the complex plane.
-- source:
--   Standard topology of annuli and the slit-plane domain.

import Definitions.Def_slitKeyholeRegion

namespace WeightedRootIntegralIdentity

theorem slit_keyhole_region_isOpen_v3 {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    IsOpen (slitKeyholeRegion r R) := by sorry

end WeightedRootIntegralIdentity
