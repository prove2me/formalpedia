-- Prove2me | Theorems.Thm_P2M_GlobalTheory_FibreStalk_ker_stalkMap_fiber__bc23ea83ee2b
-- name    : P2M_GlobalTheory_FibreStalk_ker_stalkMap_fiber__bc23ea83ee2b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T00:04:59.366417+00:00
-- url     : https://prove2.me/theorems/3b206cb9-770a-4598-b7b7-6c15766a2288
-- title:
--   P2 M Global Theory Fibre Stalk ker stalk Map fiber  bc23ea83ee2b: P2 M Global Theory Fibre Stalk ker stalk Map fiber  bc23ea83ee2b
-- statement:
--   The P2 M Global Theory Fibre Stalk ker stalk Map fiber  bc23ea83ee2b construction uses the P2 M Global Theory Fibre Stalk ker stalk Map fiber  bc23ea83ee2b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingKrullDimFiberStalkEqQuotient.lean#L17-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RingKrullDimFiberStalkEqQuotient.lean#L17-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingKrullDimFiberStalkEqQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory
open GlobalTheory GlobalTheory.FibreStalk

theorem P2M_GlobalTheory_FibreStalk_ker_stalkMap_fiber__bc23ea83ee2b (B Y : Scheme.{0}) (π : Y ⟶ B) (b : B) (z : π.fiber b) :
    RingHom.ker ((π.fiberι b).stalkMap z).hom =
      (IsLocalRing.maximalIdeal (B.presheaf.stalk (π (π.fiberι b z)))).map
        (π.stalkMap (π.fiberι b z)).hom := by sorry

alias «GlobalTheory».«FibreStalk».«ker_stalkMap_fiberι» := P2M_GlobalTheory_FibreStalk_ker_stalkMap_fiber__bc23ea83ee2b
