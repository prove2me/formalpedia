-- Prove2me | Theorems.Thm_P2M_Bl_general_b_fact_left______goal1_a57afc021d90
-- name    : P2M_Bl_general_b_fact_left______goal1_a57afc021d90
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:30.43826+00:00
-- url     : https://prove2.me/theorems/692dcd35-a936-4959-b4b5-7dfae7508a31
-- title:
--   P2 M Bl general b fact left      goal1 a57afc021d90: P2 M Bl general b fact left      goal1 a57afc021d90
-- statement:
--   The P2 M Bl general b fact left      goal1 a57afc021d90 construction uses the P2 M Bl general b fact left      goal1 a57afc021d90 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeftSide/Imports.lean#L50-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactLeftSide/Imports.lean#L50-L77

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactLeftSide_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_left'''''

theorem P2M_Bl_general_b_fact_left______goal1_a57afc021d90 :
  ∀ {O A I : Type} [inst : CommRing.{0} O] [inst_1 : CommRing.{0} A] [inst_2 : Algebra.{0, 0} O A]
  [inst_3 : Fintype.{0} I] [DecidableEq.{1} I] {B : I → Type} [inst_5 : (i : I) → AddCommGroup.{0} (B i)]
  [inst_6 : (i : I) → Module.{0, 0} O (B i)] (ε : (i : I) → LinearMap.{0, 0, 0, 0} (RingHom.id.{0} O) (B i) A)
  (T : (i : I) → Set.{0} (B i)),
  Eq.{1}
    (Submodule.span.{0, 0} O
      (Set.ofPred.{0} fun (X : A) ↦
        Exists.{1} fun (F : (i : I) → B i) ↦
          And (∀ (i : I), Membership.mem.{0, 0} (Submodule.span.{0, 0} O (T i)) (F i))
            (Eq.{1} X (Finset.prod.{0, 0} Finset.univ.{0} fun (i : I) ↦ DFunLike.coe.{1, 1, 1} (ε i) (F i)))))
    (Submodule.span.{0, 0} O
      (Set.ofPred.{0} fun (X : A) ↦
        Exists.{1} fun (F : (i : I) → B i) ↦
          And (∀ (i : I), Membership.mem.{0, 0} (T i) (F i))
            (Eq.{1} X (Finset.prod.{0, 0} Finset.univ.{0} fun (i : I) ↦ DFunLike.coe.{1, 1, 1} (ε i) (F i))))) := by sorry

alias «Bl».«general_b_fact_left'''''».«goal1» := P2M_Bl_general_b_fact_left______goal1_a57afc021d90
