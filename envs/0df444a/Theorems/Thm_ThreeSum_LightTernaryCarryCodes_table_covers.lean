-- Prove2me | Theorems.Thm_ThreeSum_LightTernaryCarryCodes_table_covers
-- name    : ThreeSum.LightTernaryCarryCodes.table_covers
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T11:00:45.907332+00:00
-- url     : https://prove2.me/theorems/71405e40-5e91-4dd3-9120-4e0fa396863f
-- title:
--   Light Ternary Carry Codes: table covers
-- statement:
--   The Light Ternary Carry Codes construction uses the table covers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryCodes.lean#L264-L275
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryCarryCodes.lean#L264-L275

import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDigits
import Definitions.Def_Submission_ThreeSum_TernaryCarryCode
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_ThreeSum_LightTernaryCarryCodes
set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryCarryCodes
open Light TernarySignedDigits
set_option maxHeartbeats 2400000
set_option maxRecDepth 9000
variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}

theorem ThreeSum.LightTernaryCarryCodes.table_covers {ν : ℕ → ℤ} {dst J : ℕ}
    (h : Table ν dst J (2^J)) {c : CarryWord J}
    (hc : ValidCarry c) :
    ∃ q<2^J, accepted J q=1 ∧ ∀ i : Fin (J+1),
      ν (dst+q*(J+1)+J-i.val)=((c i).val : ℤ) := by sorry
