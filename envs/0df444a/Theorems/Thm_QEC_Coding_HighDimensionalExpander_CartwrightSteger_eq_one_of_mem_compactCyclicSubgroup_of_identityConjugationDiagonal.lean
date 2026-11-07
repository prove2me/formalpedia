-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_eq_one_of_mem_compactCyclicSubgroup_of_identityConjugationDiagonal
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.eq_one_of_mem_compactCyclicSubgroup_of_identityConjugationDiagonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:19:56.742363+00:00
-- url     : https://prove2.me/theorems/55ff6eb2-6bab-4e34-a19d-b7dccc75ceda
-- title:
--   Cartwright Steger: eq one of mem compact Cyclic Subgroup of identity Conjugation Diagonal
-- statement:
--   LSV05b Proposition 4.8's compact obstruction, separated cleanly from
--   the forthcoming global arithmetic inclusion: an element of the explicit
--   compact cyclic subgroup satisfying the construction-owned infinity
--   diagonal condition is necessarily trivial.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L695-L706
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/BuildingStabilizer.lean#L695-L706

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingAction
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_BuildingStabilizer
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.eq_one_of_mem_compactCyclicSubgroup_of_identityConjugationDiagonal
    (P : BasePrime) (r : Rank)
    (g : Matrix.ProjGenLinGroup (Fin r.matrixRank) (BuildingLocalField P))
    (hg : g ∈ BuildingCompactCyclicSubgroup P r)
    (hdiag : BuildingElementHasIdentityConjugationDiagonal P r g) :
    g = 1 := by sorry
