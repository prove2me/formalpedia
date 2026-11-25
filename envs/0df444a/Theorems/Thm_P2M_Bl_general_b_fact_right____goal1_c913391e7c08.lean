-- Prove2me | Theorems.Thm_P2M_Bl_general_b_fact_right____goal1_c913391e7c08
-- name    : P2M_Bl_general_b_fact_right____goal1_c913391e7c08
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:52:25.204477+00:00
-- url     : https://prove2.me/theorems/09cbf75e-dcb5-43ce-bffa-fe52899a4132
-- title:
--   P2 M Bl general b fact right    goal1 c913391e7c08: P2 M Bl general b fact right    goal1 c913391e7c08
-- statement:
--   The P2 M Bl general b fact right    goal1 c913391e7c08 construction uses the P2 M Bl general b fact right    goal1 c913391e7c08 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightExtra/Imports.lean#L5-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/GeneralBFactRightExtra/Imports.lean#L5-L29

import Mathlib
import Definitions.Def_Lemmata_GeneralBFactRightExtra_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.general_b_fact_right'''

theorem P2M_Bl_general_b_fact_right____goal1_c913391e7c08 :
  ∀ {K : Type} [inst : NormedField.{0} K] [IsUltrametricDist.{0} K] {p : Nat} {a b : K},
  LE.le.{0} (Norm.norm.{0} a) 1 →
    LE.le.{0} (Norm.norm.{0} b) 1 →
      LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} a b)) (Inv.inv.{0} (Nat.cast.{0} p)) →
        ∀ (k : Nat),
          LE.le.{0} (Norm.norm.{0} (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} a k) (HPow.hPow.{0, 0, 0} b k)))
            (Inv.inv.{0} (Nat.cast.{0} p)) := by sorry

alias «Bl».«general_b_fact_right'''».«goal1» := P2M_Bl_general_b_fact_right____goal1_c913391e7c08
