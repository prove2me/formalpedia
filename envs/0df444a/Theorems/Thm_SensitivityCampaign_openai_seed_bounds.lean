-- Prove2me | Theorems.Thm_SensitivityCampaign_openai_seed_bounds
-- name    : SensitivityCampaign.openai_seed_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-15T17:43:18.781766+00:00
-- url     : https://prove2.me/theorems/f7bde5fc-d080-491e-979b-b6690f87a313
-- title:
--   OpenAI’s general finite seed bounds
-- statement:
--   For integers $d\ge1$ and $M\ge9^{d+1}$, there is a total Boolean function $f$ with $f(0)=0$, $s(f)\le2(d+2)M^{d+1}$, and $bs(f,0)\ge M^2(2M^2+1)^d$. Here $0$ denotes the all-zero input. This packages the existing OpenAI construction while leaving the coordinate dimension existential.
-- source:
--   https://github.com/bigospeedrun/site/issues/2

import Mathlib
import Definitions.Def_SensitivityCampaign
open OAI.Paper320

theorem SensitivityCampaign.openai_seed_bounds
    (d M : ℕ) (hd : 1 ≤ d) (hM : 9 ^ (d + 1) ≤ M) :
    ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      f (fun _ => false) = false ∧
      sensitivity f ≤ 2 * (d + 2) * M ^ (d + 1) ∧
      M ^ 2 * (2 * M ^ 2 + 1) ^ d ≤
        blockSensitivityAt f (fun _ => false) := by sorry
