-- Prove2me | Theorems.Thm_PalomarDimitrov_conjecture1EqualityIffPrime
-- name    : PalomarDimitrov.conjecture1EqualityIffPrime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:58:03.234886+00:00
-- url     : https://prove2.me/theorems/a1a8380d-97f0-5c06-8e7e-b17363e714ca
-- title:
--   Palomar Dimitrov: conjecture1 Equality Iff Prime
-- statement:
--   Proved equality characterization for Dimitrov's Conjecture 1.
--
--   Source: https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/Solution.lean#L42-L53
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/Solution.lean#L42-L53

import Definitions.Def_FrontierMathLean_DimitrovConjecture1Equality
import Definitions.Def_FrontierMathLean_DimitrovConjecture3Equality
import Definitions.Def_DimitrovConjectures_Solution
set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.sigma
open PalomarDimitrov

theorem PalomarDimitrov.conjecture1EqualityIffPrime (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    ((5 * ((n : ℚ) ^ 2 - 1) ^ k
          + 2 * ((n : ℚ) + 1) ^ (2 * k)
          + 2 * ((n : ℚ) - 1) ^ (2 * k)) /
        (((n : ℚ) ^ 2 - 1) ^ k) =
      ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k
          + (sigmaOne n : ℚ) ^ k) *
        (((n.totient : ℚ) ^ k)⁻¹ + ((dedekindPsi n : ℚ) ^ k)⁻¹
          + ((sigmaOne n : ℚ) ^ k)⁻¹)) ↔
      n.Prime := by sorry
