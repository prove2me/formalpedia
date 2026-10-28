-- Prove2me | Theorems.Thm_Sensitivity213303_actual_seeds
-- name    : Sensitivity213303.actual_seeds
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:06:15.476516+00:00
-- url     : https://prove2.me/theorems/6b8d2694-d295-4d3b-8450-fe94d5221bae
-- title:
--   Sensitivity separation 2.13303: seed
-- statement:
--   For every natural number $m$, there is a total Boolean function $f$ on some $n$ bits satisfying $16^m\le s(f)\le 10^{69}\,31739938^m$ and $bs(f)\ge (10007^4)^m$. Here $s$ and $bs$ denote sensitivity and block sensitivity. These actual seed functions imply the campaign's asymptotic exponent bound.
-- source:
--   Verified attached Lean checkpoint, Endpoint40Complete.lean and Endpoint40Mission.lean; https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_SensitivitySeparation
set_option autoImplicit false

theorem Sensitivity213303.actual_seeds : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
  16^m ≤ OAI.Paper320.sensitivity f ∧
  OAI.Paper320.sensitivity f ≤ 10^69*31739938^m ∧
  (10007^4)^m ≤ OAI.Paper320.blockSensitivity f := by sorry
