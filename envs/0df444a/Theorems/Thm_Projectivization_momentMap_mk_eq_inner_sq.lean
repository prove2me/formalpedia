-- Prove2me | Theorems.Thm_Projectivization_momentMap_mk_eq_inner_sq
-- name    : Projectivization.momentMap_mk_eq_inner_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:35.53556+00:00
-- url     : https://prove2.me/theorems/3be5d2fc-bb18-4798-98ec-d8883cb39f30
-- title:
--   Projectivization: moment Map mk eq inner sq
-- statement:
--   **The moment coordinate is a squared overlap.** For a unit vector `ψ`, the `i`-th coordinate
--   of the moment map at `[ψ]` equals `‖⟨eᵢ, ψ⟩‖²` for the standard basis vector
--   `eᵢ = EuclideanSpace.single i 1`.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/MomentMap.lean#L78-L82
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/MomentMap.lean#L78-L82

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

theorem Projectivization.momentMap_mk_eq_inner_sq (ψ : EuclideanSpace ℂ ι) (hψ0 : ψ ≠ 0)
    (hψ : ‖ψ‖ = 1) (i : ι) :
    momentMap (mk ℂ ψ hψ0) i = ‖inner ℂ (EuclideanSpace.single i (1 : ℂ)) ψ‖ ^ 2 := by sorry
