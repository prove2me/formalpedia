-- Prove2me | Theorems.Thm_P2M_GlobalTheory_CMLattice____ne_zero_814f16d1d8c8
-- name    : P2M_GlobalTheory_CMLattice____ne_zero_814f16d1d8c8
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:02:17.4791+00:00
-- url     : https://prove2.me/theorems/acdbd8b0-b158-483c-91f3-fbd4f4a84eb7
-- title:
--   P2 M Global Theory CMLattice    ne zero 814f16d1d8c8: P2 M Global Theory CMLattice    ne zero 814f16d1d8c8
-- statement:
--   The P2 M Global Theory CMLattice    ne zero 814f16d1d8c8 construction uses the P2 M Global Theory CMLattice    ne zero 814f16d1d8c8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeCmEqIdealAndCovolume.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CubicalLineBundles/LatticeCmEqIdealAndCovolume.lean#L25-L26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
open GlobalTheory.CMLattice
variable {K : Type} [Field K] [NumberField K]

theorem P2M_GlobalTheory_CMLattice____ne_zero_814f16d1d8c8 (L : PeriodPair) : L.ω₁ ≠ 0 := by sorry

alias «GlobalTheory».«CMLattice».«ω₁_ne_zero» := P2M_GlobalTheory_CMLattice____ne_zero_814f16d1d8c8
