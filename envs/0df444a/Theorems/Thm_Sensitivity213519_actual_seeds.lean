-- Prove2me | Theorems.Thm_Sensitivity213519_actual_seeds
-- name    : Sensitivity213519.actual_seeds
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:25:48.193257+00:00
-- url     : https://prove2.me/theorems/605418a9-c4c3-4764-a223-32aa86b486b8
-- title:
--   Sensitivity separation 2.13519: seed
-- statement:
--   For every natural number $m$, there is a total Boolean function $f$ on some $n$ bits satisfying $16^m\le s(f)\le 10^{69}\,31192129^m$ and $bs(f)\ge (10007^4)^m$. Here $s$ and $bs$ denote sensitivity and block sensitivity. These actual seed functions imply the campaign's asymptotic exponent bound.
-- source:
--   Verified attached Lean checkpoint, Endpoint16CampaignComplete.lean and Endpoint16Mission.lean; https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_SensitivitySeparation
set_option autoImplicit false

theorem Sensitivity213519.actual_seeds : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
  16^m ≤ OAI.Paper320.sensitivity f ∧
  OAI.Paper320.sensitivity f ≤ 10^69*31192129^m ∧
  (10007^4)^m ≤ OAI.Paper320.blockSensitivity f := by sorry
