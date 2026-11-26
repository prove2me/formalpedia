-- Prove2me | Theorems.Thm_Scott1972_ContinuousLattice_scottExtend_maximal
-- name    : Scott1972.ContinuousLattice.scottExtend_maximal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T05:30:32.270156+00:00
-- url     : https://prove2.me/theorems/12962bd9-9f2d-58fc-adee-a503b8620221
-- title:
--   Continuous Lattice: scott Extend maximal
-- statement:
--   **Maximality clause of Scott 1972, Proposition 3.8.** Any continuous solution `f'` of
--   `f' ∘ e = f` lies below `scottExtend e f`. Following Scott: expand `f'` via
--   `continuous_eq_sSup_openInfs`, restrict each meet from `U` to the embedded subspace `e(X) ∩ U`
--   (only enlarging the meet), and recognize the result as a defining term of `scottExtend`.
--
--   Source: https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L357-L367
-- source:
--   https://github.com/catskillsresearch/scott1972/blob/278ba1745b6fb023fc3e9ffe53b7106ce60222c1/Scott1972/ContinuousLattice/Constructions.lean#L357-L367

import Definitions.Def_Scott1972_ContinuousLattice_MilnerCorrection
import Definitions.Def_Scott1972_ContinuousLattice_ScottMaps
import Definitions.Def_Scott1972_ContinuousLattice_Injective
import Mathlib.Order.Preorder.Finite
import Definitions.Def_Scott1972_ContinuousLattice_Constructions
set_option autoImplicit true
open Scott1972 Scott1972.ContinuousLattice
open Topology Set
variable {D : Type*} [CompleteLattice D]
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {E : Type*} [CompleteLattice E]

theorem Scott1972.ContinuousLattice.scottExtend_maximal (hE : IsContinuousLattice E) (e : X → Y) {f : X → E} {f' : Y → E}
    (hf' : @Continuous Y E _ scottTopologicalSpace f') (h_ext : ∀ x, f' (e x) = f x) (y : Y) :
    f' y ≤ scottExtend e f y := by sorry
