-- Prove2me | Theorems.Thm_P2M_GlobalTheory_OnePoint_exists_eq_C_of_eval__eq_zero_f49c21f6d652
-- name    : P2M_GlobalTheory_OnePoint_exists_eq_C_of_eval__eq_zero_f49c21f6d652
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:06:38.211998+00:00
-- url     : https://prove2.me/theorems/71a26fbb-3242-4e21-8d5f-2e3e86f86f55
-- title:
--   P2 M Global Theory One Point exists eq C of eval  eq zero f49c21f6d652: P2 M Global Theory One Point exists eq C of eval  eq zero f49c21f6d652
-- statement:
--   The P2 M Global Theory One Point exists eq C of eval  eq zero f49c21f6d652 construction uses the P2 M Global Theory One Point exists eq C of eval  eq zero f49c21f6d652 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L106-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IsIntegrallyClosedInFractionFieldPowerSeries.lean#L106-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
variable {K : Type u} [Field K]

theorem P2M_GlobalTheory_OnePoint_exists_eq_C_of_eval__eq_zero_f49c21f6d652 {x : K⸨X⸩} {p : Polynomial K} (hp : p ≠ 0)
    (hx : p.eval₂ (HahnSeries.C : K →+* K⸨X⸩) x = 0) : ∃ c : K, x = HahnSeries.C c := by sorry

alias «GlobalTheory».«OnePoint».«exists_eq_C_of_eval₂_eq_zero» := P2M_GlobalTheory_OnePoint_exists_eq_C_of_eval__eq_zero_f49c21f6d652
