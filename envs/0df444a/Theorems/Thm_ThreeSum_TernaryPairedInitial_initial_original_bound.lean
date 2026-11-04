-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedInitial_initial_original_bound
-- name    : ThreeSum.TernaryPairedInitial.initial_original_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:55.644091+00:00
-- url     : https://prove2.me/theorems/f37ab008-0836-49c7-8cf6-aacd0272c51e
-- title:
--   Ternary Paired Initial: initial original bound
-- statement:
--   The Ternary Paired Initial construction uses the initial original bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedInitial.lean#L22-L36
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedInitial.lean#L22-L36

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitial
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedInitial
open Finset Matrix TernaryPairedPotential
open scoped BigOperators

theorem ThreeSum.TernaryPairedInitial.initial_original_bound {P G : Type*} [Fintype P] [Fintype G]
    (K Λ b n carries : ℕ) (A : G → (Fin K → P) → Matrix (Fin (2*K)) (Fin Λ) ℤ)
    (hA : ∀ g e i j, (A g e i j).natAbs≤b)
    (hG : Fintype.card G≤n*carries) (hP : Fintype.card P≤n^2) :
    (∑ g : G, ∑ e : Fin K → P, minorWeight (A g e)) ≤
      n^(2*K+1)*carries*Λ^(2*K)*((2*K).factorial*b^(2*K))^2 := by sorry
