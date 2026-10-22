-- Prove2me | Theorems.Thm_SensitivityProfileCycle_finite_seeds
-- name    : SensitivityProfileCycle.finite_seeds
-- status  : Proved
-- author  : @dmilosch
-- created : 2026-10-21T21:21:47.788348+00:00
-- url     : https://prove2.me/theorems/dd31034a-13ba-4d9d-8e2f-0087ac70bad8
-- title:
--   A finite profile cycle constructs Boolean seeds at every repetition
-- statement:
--   Let $c$ be a finite recursive-profile cycle certificate, with tournament size $K$, positive period $p$, and return factor $R$. There exists a natural number $C>1$, independent of the repetition count, such that for every natural number $m$ there is a total Boolean function $f_m$ on a finite cube satisfying
--
--   $$s(f_m)\le C R^m,\qquad \operatorname{bs}(f_m,0)\ge (K^p)^m.$$
--
--   The dimension may depend on $m$. The zero input is the all-false vector. No assumption that the certificate crosses any particular separation exponent is needed. This theorem turns finite graph and integer-profile checks into genuine Boolean functions and is reusable for other numerical targets.
-- source:
--   Original variable-cycle generalization of the recursive bounds in accepted Prove2Me submission a9d25c46-43bd-4fb1-826b-0ed075b8cf0a, https://prove2.me/theorems/46659a00-722d-4dc9-b28e-ef02d6a0c9c2, namespaces SensitivityNQ and SensitivitySourceCombinedPeriodic, especially profile_step_bounds and stage_blocks. Source authors: yousofy with Codex; retains the attributed OpenAI/math, Robin Kothari with Codex, and earlier community foundations. Mission motivation: https://github.com/bigospeedrun/site/issues/2. The source does not prove that this generalization attains 2.15.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivityProfileCycle

theorem SensitivityProfileCycle.finite_seeds
    (c : SensitivityProfileCycle.Certificate) :
    ∃ C : ℕ, 1 < C ∧ ∀ m : ℕ,
      ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
        OAI.Paper320.sensitivity f ≤ C * c.radius ^ m ∧
        (c.vertices ^ c.period) ^ m ≤
          OAI.Paper320.blockSensitivityAt f (fun _ => false) := by sorry
