-- Prove2me | Theorems.Thm_P2M_GlobalTheory__Multi_mem_regForms_c782fe77fe92
-- name    : P2M_GlobalTheory__Multi_mem_regForms_c782fe77fe92
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:41.675726+00:00
-- url     : https://prove2.me/theorems/c44025cc-dbab-43a1-b03f-f85b228cc1a6
-- title:
--   P2 M Global Theory  Multi mem reg Forms c782fe77fe92: P2 M Global Theory  Multi mem reg Forms c782fe77fe92
-- statement:
--   The P2 M Global Theory  Multi mem reg Forms c782fe77fe92 construction uses the P2 M Global Theory  Multi mem reg Forms c782fe77fe92 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L117-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L117-L121

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

theorem P2M_GlobalTheory__Multi_mem_regForms_c782fe77fe92 (w : Fin p → Ω[F⁄K])
    (hw : ∀ k, w k ∈ LinearMap.range (KaehlerDifferential.map K K V F)) :
    exteriorPower.ιMulti F p w ∈ regForms K V F p := by sorry

alias «GlobalTheory».«ιMulti_mem_regForms» := P2M_GlobalTheory__Multi_mem_regForms_c782fe77fe92
