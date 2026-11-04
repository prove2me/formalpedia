-- Prove2me | Theorems.Thm_ThreeSum_TernaryPairedInitial_initial_fourth_bound
-- name    : ThreeSum.TernaryPairedInitial.initial_fourth_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-03T10:07:42.576859+00:00
-- url     : https://prove2.me/theorems/90ea4c4b-a0b7-453f-80f6-aa7bf8193000
-- title:
--   Ternary Paired Initial: initial fourth bound
-- statement:
--   Carry and logarithmic factors only need one additional power of n
--   AFTER taking the fourth power. The determinant coefficient is fixed.
--
--   Source: https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedInitial.lean#L40-L58
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedInitial.lean#L40-L58

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Definitions.Def_Submission_ThreeSum_TernaryPairedInitial
set_option autoImplicit false
open ThreeSum ThreeSum.TernaryPairedInitial
open Finset Matrix TernaryPairedPotential
open scoped BigOperators

theorem ThreeSum.TernaryPairedInitial.initial_fourth_bound {P G : Type*} [Fintype P] [Fintype G]
    (K Λ b n carries C : ℕ) (A : G → (Fin K → P) → Matrix (Fin (2*K)) (Fin Λ) ℤ)
    (hA : ∀ g e i j, (A g e i j).natAbs≤b)
    (hG : Fintype.card G≤n*carries) (hP : Fintype.card P≤n^2)
    (hcarry : carries^4*Λ^(8*K)≤C*n) :
    (∑ g : G, ∑ e : Fin K → P, minorWeight (A g e))^4 ≤
      (C*((2*K).factorial*b^(2*K))^8)*n^(8*K+5) := by sorry
