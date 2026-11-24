-- Prove2me | Theorems.Thm_P2M_GlobalTheory_eq_lift_det_smul__Multi_7c34f112c031
-- name    : P2M_GlobalTheory_eq_lift_det_smul__Multi_7c34f112c031
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:51.171035+00:00
-- url     : https://prove2.me/theorems/74a321af-be47-473a-a108-a90bf3497213
-- title:
--   P2 M Global Theory eq lift det smul  Multi 7c34f112c031: P2 M Global Theory eq lift det smul  Multi 7c34f112c031
-- statement:
--   The P2 M Global Theory eq lift det smul  Multi 7c34f112c031 construction uses the P2 M Global Theory eq lift det smul  Multi 7c34f112c031 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L40-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasisKaehlerOfAlgebraicIndependent.lean#L40-L55

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
variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [Fintype ι] [DecidableEq ι]

theorem P2M_GlobalTheory_eq_lift_det_smul__Multi_7c34f112c031 {n : ℕ} (b : Basis (Fin n) R M) (η : ⋀[R]^n M) :
    η = exteriorPower.alternatingMapLinearEquiv b.det η • exteriorPower.ιMulti R n b := by sorry

alias «GlobalTheory».«eq_lift_det_smul_ιMulti» := P2M_GlobalTheory_eq_lift_det_smul__Multi_7c34f112c031
