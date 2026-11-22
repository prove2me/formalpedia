-- Prove2me | Theorems.Thm_Projectivization_momentRatio_smul
-- name    : Projectivization.momentRatio_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:33.308794+00:00
-- url     : https://prove2.me/theorems/4f24b803-5a41-46dd-adf7-4cfbd544626f
-- title:
--   Projectivization: moment Ratio smul
-- statement:
--   The coordinate ratio `‖vᵢ‖²/‖v‖²` is invariant under nonzero rescaling of `v`
--   (the projective well-definedness of `momentMap`).
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/MomentMap.lean#L58-L61
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/MomentMap.lean#L58-L61

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

theorem Projectivization.momentRatio_smul (c : ℂ) (hc : c ≠ 0) (v : EuclideanSpace ℂ ι) (i : ι) :
    ‖(c • v) i‖ ^ 2 / ‖c • v‖ ^ 2 = ‖v i‖ ^ 2 / ‖v‖ ^ 2 := by sorry
