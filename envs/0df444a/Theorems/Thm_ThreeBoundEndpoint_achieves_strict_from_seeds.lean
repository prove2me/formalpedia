-- Prove2me | Theorems.Thm_ThreeBoundEndpoint_achieves_strict_from_seeds
-- name    : ThreeBoundEndpoint.achieves_strict_from_seeds
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-25T22:37:46.171252+00:00
-- url     : https://prove2.me/theorems/fb153e3d-f5b1-40d6-b3a2-03b1279642ca
-- title:
--   Exponential Boolean seed families imply a sensitivity separation
-- statement:
--   Let \(c,r,g,t>1\) be natural numbers, and let \(\beta\ge0\) satisfy \(\beta<\log g/\log r\). Suppose that for every \(m\ge0\) there is a Boolean function \(f_m\), on a finite number of input bits, such that
--   \[
--   t^m\le s(f_m)\le cr^m,\qquad bs(f_m)\ge g^m.
--   \]
--   Then \(\beta\) is achievable in the campaign sense: for every \(\varepsilon>0\) and every positive integer \(S\), some Boolean function \(f\) satisfies
--   \[
--   s(f)\ge S,\qquad bs(f)\ge s(f)^{\beta-\varepsilon}.
--   \]
--   Here \(s\) and \(bs\) denote sensitivity and block sensitivity. This theorem converts a proved seed construction into the asymptotic campaign goal.
-- source:
--   Original Lean formalization for the Prove2Me sensitivity campaign, EndpointReduction, lines 71–118; source SHA256 de30b8a2edfcd9ff563e9aac46d3fbf7ff892bcc756d3acc8fa042480e7fb56e.

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

namespace OAI.Paper320
end OAI.Paper320
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option Elab.async false
namespace ThreeBoundEndpoint
end ThreeBoundEndpoint
open ThreeBoundEndpoint
open OAI.Paper320

theorem ThreeBoundEndpoint.achieves_strict_from_seeds (c r g t : ℕ) (β : ℝ)
    (hc : 1 < c) (hr : 1 < r) (hg : 1 < g) (ht : 1 < t)
    (hβ : 0 ≤ β)
    (hstrict : β < Real.log (g : ℝ) / Real.log (r : ℝ))
    (hseed : ∀ m : ℕ, ∃ (n : ℕ) (f : (Fin n → Bool) → Bool),
      t^m ≤ sensitivity f ∧ sensitivity f ≤ c*r^m ∧ g^m ≤ blockSensitivity f) :
    SensitivityCampaign.AchievesExponent β := by sorry
