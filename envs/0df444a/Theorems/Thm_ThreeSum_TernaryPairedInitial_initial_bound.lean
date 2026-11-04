-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedInitial_initial_bound
-- name    : ThreeSum.TernaryPairedInitial.initial_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T08:09:32.695561+00:00
-- url     : https://prove2.me/theorems/992d8b22-c8f6-47d8-9cae-b71836d61bbd
-- title:
--   Ternary Paired Initial: initial bound
-- statement:
--   The Ternary Paired Initial construction uses the initial bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedInitial.lean#L10-L20
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedInitial.lean#L10-L20

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitial
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedInitial
open Finset Matrix TernaryPairedPotential
open scoped BigOperators

theorem ThreeSum.TernaryPairedInitial.initial_bound {P G : Type*} [Fintype P] [Fintype G]
    (K Λ b : ℕ) (A : G → (Fin K → P) → Matrix (Fin (2*K)) (Fin Λ) ℤ)
    (hA : ∀ g e i j, (A g e i j).natAbs≤b) :
    (∑ g : G, ∑ e : Fin K → P, minorWeight (A g e)) ≤
      Fintype.card G*Fintype.card P^K*Λ^(2*K)*((2*K).factorial*b^(2*K))^2 := by sorry
