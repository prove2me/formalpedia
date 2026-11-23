-- Prove2me | Theorems.Thm_P2M_GlobalTheory_formMap__Multi_014b852379ac
-- name    : P2M_GlobalTheory_formMap__Multi_014b852379ac
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:30.304907+00:00
-- url     : https://prove2.me/theorems/4a370c2a-057c-4b18-a00c-2e507de3e56c
-- title:
--   P2 M Global Theory form Map  Multi 014b852379ac: P2 M Global Theory form Map  Multi 014b852379ac
-- statement:
--   The P2 M Global Theory form Map  Multi 014b852379ac construction uses the P2 M Global Theory form Map  Multi 014b852379ac property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L108-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L108-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (K V F : Type*) [CommRing K] [CommRing V] [CommRing F] [Algebra K V] [Algebra V F]
  [Algebra K F] [IsScalarTower K V F] (p : ℕ)
variable {V p}

theorem P2M_GlobalTheory_formMap__Multi_014b852379ac (v : Fin p → Ω[V⁄K]) :
    formMap K V F p (exteriorPower.ιMulti V p v)
      = exteriorPower.ιMulti F p (fun k => KaehlerDifferential.map K K V F (v k)) := by sorry

alias «GlobalTheory».«formMap_ιMulti» := P2M_GlobalTheory_formMap__Multi_014b852379ac
