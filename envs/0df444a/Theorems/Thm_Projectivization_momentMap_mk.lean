-- Prove2me | Theorems.Thm_Projectivization_momentMap_mk
-- name    : Projectivization.momentMap_mk
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:27.734578+00:00
-- url     : https://prove2.me/theorems/90101ec0-36b7-4aad-ba6b-09dd7d498cfc
-- title:
--   Projectivization: moment Map mk
-- statement:
--   The moment map evaluated at a representative `ψ`: `Φ([ψ])ᵢ = ‖ψᵢ‖²/‖ψ‖²`.
--   The value depends only on `ψ` (not on the chosen `rep`), by scale invariance.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/MomentMap.lean#L66-L73
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/MomentMap.lean#L66-L73

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MeasureSpace
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MomentMap
set_option autoImplicit false
@[expose] public section
public section
open scoped LinearAlgebra.Projectivization
open Projectivization
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]

theorem Projectivization.momentMap_mk (ψ : EuclideanSpace ℂ ι) (hψ : ψ ≠ 0) (i : ι) :
    momentMap (mk ℂ ψ hψ) i = ‖ψ i‖ ^ 2 / ‖ψ‖ ^ 2 := by sorry
