-- Prove2me | Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_infix_atomization
-- name    : QEC.Locality.DaiLiHorizontalAtomization.infix_atomization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T16:51:00.726476+00:00
-- url     : https://prove2.me/theorems/38a75112-ebd1-4fa9-a1e4-b6c7370d9936
-- title:
--   Dai Li Horizontal Atomization: infix atomization
-- statement:
--   Every nonempty contiguous infix of an atomization is a valid atomization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1168-L1197
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1168-L1197

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

theorem QEC.Locality.DaiLiHorizontalAtomization.infix_atomization
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms group : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hGroup : group <:+: atoms) (hGroupNe : group ≠ []) :
    DaiLiHorizontalAtomization support ell (daiLiAtomGroupLower group)
      (daiLiAtomGroupUpper group) group := by sorry
