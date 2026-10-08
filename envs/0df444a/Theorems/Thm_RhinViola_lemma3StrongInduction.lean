-- Prove2me | Theorems.Thm_RhinViola_lemma3StrongInduction
-- name    : RhinViola.lemma3StrongInduction
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T00:17:05.403821+00:00
-- url     : https://prove2.me/theorems/7ad5605e-62da-407e-907b-7e8bf492976b
-- title:
--   Strong-induction principle matching the Rhin-Viola Lemma 3 descent
-- statement:
--   To prove a property for every triple k,l,nu with nu≤k+l, it is enough to prove the four boundary configurations k=0, l=0, nu=0, or nu=k+l, and prove the three-branch recurrence step from (k-1,l-1,nu-1), (k,l-1,nu), and (k-1,l,nu). Strong induction on k+l+nu terminates because each branch strictly lowers that measure in the interior.
-- source:
--   Formal induction principle extracted from the descent argument in G. Rhin and C. Viola, On the irrationality measure of zeta(2), Annales de l'Institut Fourier 43 (1993), Lemma 3, p. 90.

import Mathlib.Tactic

theorem RhinViola.lemma3StrongInduction
    (P : ℕ → ℕ → ℕ → Prop)
    (hbase : ∀ k l nu : ℕ, nu ≤ k + l →
      (k = 0 ∨ l = 0 ∨ nu = 0 ∨ nu = k + l) → P k l nu)
    (hstep : ∀ k l nu : ℕ,
      0 < k → 0 < l → 0 < nu → nu < k + l →
      P (k - 1) (l - 1) (nu - 1) →
      P k (l - 1) nu →
      P (k - 1) l nu →
      P k l nu) :
    ∀ k l nu : ℕ, nu ≤ k + l → P k l nu := by sorry
