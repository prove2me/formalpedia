-- Prove2me | Theorems.Thm_RhinViola_lemma3BaseCaseClassification
-- name    : RhinViola.lemma3BaseCaseClassification
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T00:15:02.233908+00:00
-- url     : https://prove2.me/theorems/fd900433-ae4e-4598-a7cb-9d555f85d618
-- title:
--   Base-case classification for the Rhin-Viola Lemma 3 descent
-- statement:
--   Under the balance nu+r=k+l, if at least one of k,l,nu,r vanishes then the Lemma 3 recursion is in one of the paper's base configurations: nu=0 (Lemma 1); l=0 with nu≤k (J1); k=0 with nu≤l (J1 after swapping variables); or r=0 with positive k,l, where nu=k+l and both k,l are strictly smaller than nu (J2).
-- source:
--   G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Lemmas 1-3, pp. 87-90.

import Mathlib.Tactic

theorem RhinViola.lemma3BaseCaseClassification
    (k l nu r : ℕ) (hbal : nu + r = k + l)
    (hzero : k = 0 ∨ l = 0 ∨ nu = 0 ∨ r = 0) :
    nu = 0 ∨
      (l = 0 ∧ nu ≤ k) ∨
      (k = 0 ∧ nu ≤ l) ∨
      (r = 0 ∧ 0 < k ∧ 0 < l ∧ nu = k + l ∧ k < nu ∧ l < nu) := by sorry
