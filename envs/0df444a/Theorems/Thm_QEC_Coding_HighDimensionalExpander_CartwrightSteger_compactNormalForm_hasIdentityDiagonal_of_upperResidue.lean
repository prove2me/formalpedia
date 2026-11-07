-- Prove2me | Theorems.Thm_QEC_Coding_HighDimensionalExpander_CartwrightSteger_compactNormalForm_hasIdentityDiagonal_of_upperResidue
-- name    : QEC.Coding.HighDimensionalExpander.CartwrightSteger.compactNormalForm_hasIdentityDiagonal_of_upperResidue
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T13:33:57.391207+00:00
-- url     : https://prove2.me/theorems/12038762-e319-4178-ba6a-5b64ffaba96c
-- title:
--   Cartwright Steger: compact Normal Form has Identity Diagonal of upper Residue
-- statement:
--   The upper-unipotent infinity condition forces every diagonal block of
--   a global compact normal form to be the identity.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1726-L1753
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HighDimensionalExpander/CartwrightSteger/Building/InfinityLattice.lean#L1726-L1753

import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityAction
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.FieldTheory.RatFunc.Valuation
import Definitions.Def_QEC_Coding_HighDimensionalExpander_CartwrightSteger_Building_InfinityLattice
set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.HighDimensionalExpander QEC.Coding.HighDimensionalExpander.CartwrightSteger
attribute [local instance] QEC.Coding.HighDimensionalExpander.CartwrightSteger._p2m_local_instance_a53544448f_18

theorem QEC.Coding.HighDimensionalExpander.CartwrightSteger.compactNormalForm_hasIdentityDiagonal_of_upperResidue
    (P : BasePrime) (r : Rank) (u : (ConstantExtension P r)ˣ)
    (j : ℕ)
    (hupper : HasUpperUnipotentInfinityResidue P r
      (globalCompactNormalForm P r u j)) :
    CompactNormalFormHasIdentityDiagonal P r u j := by sorry
