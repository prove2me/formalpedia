-- Prove2me | Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_prefix_atomization
-- name    : QEC.Locality.DaiLiHorizontalAtomization.prefix_atomization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T17:06:26.848498+00:00
-- url     : https://prove2.me/theorems/1726f320-f21a-4a9d-8335-04338a1f781d
-- title:
--   Dai Li Horizontal Atomization: prefix atomization
-- statement:
--   A nonempty prefix of an atomization is itself an atomization.
--
--   Source: https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1123-L1165
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Locality/OptimalTradeoff/BadSquareSubdivision.lean#L1123-L1165

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

theorem QEC.Locality.DaiLiHorizontalAtomization.prefix_atomization
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms) :
    ∀ {initial suffix : List (ℝ × ℝ)}, atoms = initial ++ suffix → initial ≠ [] →
      DaiLiHorizontalAtomization support ell lower (daiLiAtomGroupUpper initial) initial := by sorry
