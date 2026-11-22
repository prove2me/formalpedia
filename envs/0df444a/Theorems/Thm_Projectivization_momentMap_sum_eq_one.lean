-- Prove2me | Theorems.Thm_Projectivization_momentMap_sum_eq_one
-- name    : Projectivization.momentMap_sum_eq_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:52:27.708948+00:00
-- url     : https://prove2.me/theorems/d1c839c8-615e-4ed4-a518-3b057e5b48c5
-- title:
--   Projectivization: moment Map sum eq one
-- statement:
--   The moment coordinates sum to one: the image lands in the standard simplex.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/MomentMap.lean#L49-L53
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/MomentMap.lean#L49-L53

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

theorem Projectivization.momentMap_sum_eq_one (p : ℙ ℂ (EuclideanSpace ℂ ι)) :
    ∑ i, momentMap p i = 1 := by sorry
