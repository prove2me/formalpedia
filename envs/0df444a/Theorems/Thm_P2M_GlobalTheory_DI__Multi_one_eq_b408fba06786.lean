-- Prove2me | Theorems.Thm_P2M_GlobalTheory_DI__Multi_one_eq_b408fba06786
-- name    : P2M_GlobalTheory_DI__Multi_one_eq_b408fba06786
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:56.572513+00:00
-- url     : https://prove2.me/theorems/5ec74736-8359-4680-bb15-8ea5ec07dc73
-- title:
--   P2 M Global Theory DI  Multi one eq b408fba06786: P2 M Global Theory DI  Multi one eq b408fba06786
-- statement:
--   The P2 M Global Theory DI  Multi one eq b408fba06786 construction uses the P2 M Global Theory DI  Multi one eq b408fba06786 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExteriorFormsSpanOfSetsMulSmulMono.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExteriorFormsSpanOfSetsMulSmulMono.lean#L31-L32

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

theorem P2M_GlobalTheory_DI__Multi_one_eq_b408fba06786 (u : Fin 1 → V) : ExteriorAlgebra.ιMulti K 1 u = ExteriorAlgebra.ι K (u 0) := by sorry

alias «GlobalTheory».«DI».«ιMulti_one_eq» := P2M_GlobalTheory_DI__Multi_one_eq_b408fba06786
