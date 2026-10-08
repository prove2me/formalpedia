-- Prove2me | Theorems.Thm_RhinViola_j1FiniteGeometricIdentity
-- name    : RhinViola.j1FiniteGeometricIdentity
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T00:19:11.54933+00:00
-- url     : https://prove2.me/theorems/0ad68354-c632-43b6-9c6c-533aff6e34a7
-- title:
--   Finite geometric difference identity for the Rhin-Viola J1 base integral
-- statement:
--   For natural a,nu, multiplying the finite sum of reflected powers (1-x)^(a+i), i=0,...,nu-1, by x gives (1-x)^a-(1-x)^(a+nu). This is the finite geometric identity that removes the apparent 1/x singularity in the J1 calculation of Rhin-Viola Lemma 2.
-- source:
--   Elementary geometric identity used implicitly in the proof of G. Rhin and C. Viola, On the irrationality measure of zeta(2), Lemma 2, p. 88.

import Mathlib.Tactic
open scoped BigOperators

theorem RhinViola.j1FiniteGeometricIdentity
    (a nu : ℕ) (x : ℝ) :
    x * Finset.sum (Finset.range nu) (fun i : ℕ => (1 - x) ^ (a + i)) =
      (1 - x) ^ a - (1 - x) ^ (a + nu) := by sorry
