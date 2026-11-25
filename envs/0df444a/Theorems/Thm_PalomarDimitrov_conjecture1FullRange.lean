-- Prove2me | Theorems.Thm_PalomarDimitrov_conjecture1FullRange
-- name    : PalomarDimitrov.conjecture1FullRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:58:00.897259+00:00
-- url     : https://prove2.me/theorems/f78e6765-6a0f-5952-885e-9abdf5d1a64c
-- title:
--   Palomar Dimitrov: conjecture1 Full Range
-- statement:
--   Proved full-range form of Dimitrov's Conjecture 1.
--
--   Source: https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/Solution.lean#L29-L39
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/Solution.lean#L29-L39

import Definitions.Def_FrontierMathLean_DimitrovConjecture1Equality
import Definitions.Def_FrontierMathLean_DimitrovConjecture3Equality
import Definitions.Def_DimitrovConjectures_Solution
set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.sigma
open PalomarDimitrov

theorem PalomarDimitrov.conjecture1FullRange (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (5 * ((n : ℚ) ^ 2 - 1) ^ k
          + 2 * ((n : ℚ) + 1) ^ (2 * k)
          + 2 * ((n : ℚ) - 1) ^ (2 * k)) /
        (((n : ℚ) ^ 2 - 1) ^ k) ≤
      ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k
          + (sigmaOne n : ℚ) ^ k) *
        (((n.totient : ℚ) ^ k)⁻¹ + ((dedekindPsi n : ℚ) ^ k)⁻¹
          + ((sigmaOne n : ℚ) ^ k)⁻¹) := by sorry
