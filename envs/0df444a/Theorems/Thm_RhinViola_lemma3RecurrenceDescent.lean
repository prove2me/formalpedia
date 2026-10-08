-- Prove2me | Theorems.Thm_RhinViola_lemma3RecurrenceDescent
-- name    : RhinViola.lemma3RecurrenceDescent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T00:12:19.924245+00:00
-- url     : https://prove2.me/theorems/19190462-f1ae-4d57-abb6-aa213ad29ab5
-- title:
--   Natural-number descent for the three Rhin-Viola Lemma 3 branches
-- statement:
--   Write r=k+l-nu. When all four quantities k,l,nu,r are positive, each of the three recursive branches in Rhin-Viola Lemma 3 preserves the balance nu+r=k+l and strictly decreases the total measure k+l+nu+r. This supplies a simple well-founded descent certificate for the paper's statement that repeated application terminates.
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Lemma 3, p. 90.

import Mathlib.Tactic

theorem RhinViola.lemma3RecurrenceDescent
    (k l nu r : ℕ)
    (hk : 0 < k) (hl : 0 < l) (hnu : 0 < nu) (hr : 0 < r)
    (hbal : nu + r = k + l) :
    (((nu - 1) + (r - 1) = (k - 1) + (l - 1)) ∧
      (k - 1) + (l - 1) + (nu - 1) + (r - 1) < k + l + nu + r) ∧
    ((nu + (r - 1) = k + (l - 1)) ∧
      k + (l - 1) + nu + (r - 1) < k + l + nu + r) ∧
    ((nu + (r - 1) = (k - 1) + l) ∧
      (k - 1) + l + nu + (r - 1) < k + l + nu + r) := by sorry
