-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DI___mul__Multi_eq_ef862d3d0758
-- name    : P2M_GlobalTheory_DI___mul__Multi_eq_ef862d3d0758
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:05:00.524222+00:00
-- url     : https://prove2.me/theorems/ecae7e5b-dbfe-4597-9389-856bf54b19cf
-- title:
--   P2 M Global Theory DI   mul  Multi eq ef862d3d0758: P2 M Global Theory DI   mul  Multi eq ef862d3d0758
-- statement:
--   The P2 M Global Theory DI   mul  Multi eq ef862d3d0758 construction uses the P2 M Global Theory DI   mul  Multi eq ef862d3d0758 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExteriorFormsSpanOfSetsMulSmulMono.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExteriorFormsSpanOfSetsMulSmulMono.lean#L25-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExteriorFormsSpanOfSetsMulSmulMono
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]

theorem P2M_GlobalTheory_DI___mul__Multi_eq_ef862d3d0758 (u : V) {q : ℕ} (w : Fin q → V) :
    ExteriorAlgebra.ι K u * ExteriorAlgebra.ιMulti K q w =
      ExteriorAlgebra.ιMulti K (q + 1) (Fin.cons u w) := by sorry

alias «GlobalTheory».«DI».«ι_mul_ιMulti_eq» := P2M_GlobalTheory_DI___mul__Multi_eq_ef862d3d0758
