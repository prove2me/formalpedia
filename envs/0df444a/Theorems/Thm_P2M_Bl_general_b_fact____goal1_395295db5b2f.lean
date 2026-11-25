-- Prove2me | Theorems.Thm_P2M_Bl_general_b_fact____goal1_395295db5b2f
-- name    : P2M_Bl_general_b_fact____goal1_395295db5b2f
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:54:02.670236+00:00
-- url     : https://prove2.me/theorems/56511284-85a8-4180-9a4d-0a4786ff838f
-- title:
--   P2 M Bl general b fact    goal1 395295db5b2f: P2 M Bl general b fact    goal1 395295db5b2f
-- statement:
--   The P2 M Bl general b fact    goal1 395295db5b2f construction uses the P2 M Bl general b fact    goal1 395295db5b2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactExtra/Imports.lean#L5-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactExtra/Imports.lean#L5-L39

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactExtra_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact'''

theorem P2M_Bl_general_b_fact____goal1_395295db5b2f :
  ∀ {K V ι Γ : Type} [inst : Field.{0} K] [inst_1 : AddCommGroup.{0} V] [inst_2 : Module.{0, 0} K V]
  (T : Γ → LinearMap.{0, 0, 0, 0} (RingHom.id.{0} K) V V) (c : ι → Γ → K) (w : ι → V),
  (∀ (i : ι), Ne.{1} (w i) 0) →
    (∀ (i : ι) (γ : Γ), Eq.{1} (DFunLike.coe.{1, 1, 1} (T γ) (w i)) (HSMul.hSMul.{0, 0, 0} (c i γ) (w i))) →
      (∀ (i j : ι), Ne.{1} i j → Exists.{1} fun (γ : Γ) ↦ Ne.{1} (c i γ) (c j γ)) → LinearIndependent.{0, 0, 0} K w := by sorry

alias «Bl».«general_b_fact'''».«goal1» := P2M_Bl_general_b_fact____goal1_395295db5b2f
