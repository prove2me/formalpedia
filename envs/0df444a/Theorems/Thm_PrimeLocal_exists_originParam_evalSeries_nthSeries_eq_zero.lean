-- Prove2me | Theorems.Thm_PrimeLocal_exists_originParam_evalSeries_nthSeries_eq_zero
-- name    : PrimeLocal.exists_originParam_evalSeries_nthSeries_eq_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T02:22:40.844261+00:00
-- url     : https://prove2.me/theorems/5178d33e-9f6b-4994-8352-8f3b16fbeb43
-- title:
--   Formal-group parameter of a p-torsion point near the origin
-- statement:
--   For a Weierstrass curve over the integers of C_p and a nonzero p-torsion point reducing to the origin, its formal-group parameter t is a zero of the evaluated p-series [p](t) of the formal group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Mathlib
import Definitions.Def_WeierstrassCurve_TorsionIntegral
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_WeierstrassCurve_FormalGroup

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WeierstrassCurve.Affine NNReal
open PowerSeries MvPowerSeries

namespace PrimeLocal
theorem exists_originParam_evalSeries_nthSeries_eq_zero (p : ℕ) [Fact p.Prime] [DecidableEq ℂ_[p]] (D : WeierstrassCurve 𝓞_ℂ_[p]) (hΔ : D.Δ ≠ 0) (F : FormalGroup 𝓞_ℂ_[p]) [F.IsComm] (hF : F.toPowerSeries = D.formalGroupLawFixed) (x y : ℂ_[p]) (h : (D.map (PadicComplexInt p).subtype).toAffine.Nonsingular x y) (hx : 1 < ‖x‖) {n : ℕ} (hn : n • (WeierstrassCurve.Affine.Point.some x y h) = 0) : ∃ t : 𝓞_ℂ_[p], (t : ℂ_[p]) = -x / y ∧ t ≠ 0 ∧ ‖(t : ℂ_[p])‖ < 1 ∧ FormalGroup.evalSeries (F.nthSeries n) t = 0 := by sorry
end PrimeLocal
