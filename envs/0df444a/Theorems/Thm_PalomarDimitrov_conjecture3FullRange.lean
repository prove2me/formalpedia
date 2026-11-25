-- Prove2me | Theorems.Thm_PalomarDimitrov_conjecture3FullRange
-- name    : PalomarDimitrov.conjecture3FullRange
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:58:21.812377+00:00
-- url     : https://prove2.me/theorems/bcd6ae65-5f83-48b4-8697-f6d3f99159dc
-- title:
--   Palomar Dimitrov: conjecture3 Full Range
-- statement:
--   Proved full-range form of Dimitrov's Conjecture 3.
--
--   Source: https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/Solution.lean#L56-L71
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/Solution.lean#L56-L71

import Definitions.Def_FrontierMathLean_DimitrovConjecture1Equality
import Definitions.Def_FrontierMathLean_DimitrovConjecture3Equality
import Definitions.Def_DimitrovConjectures_Solution
set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.sigma
open PalomarDimitrov

theorem PalomarDimitrov.conjecture3FullRange (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (4 * ((n : ℚ) + 1) ^ (2 * k)
          + (((n : ℚ) ^ 2 - 1) ^ k)
          + ((n : ℚ) - 1) ^ (2 * k)) /
        (2 * (((n : ℚ) + 1) ^ (2 * k)
          + (((n : ℚ) ^ 2 - 1) ^ k))) ≤
      (n.totient : ℚ) ^ k /
          ((dedekindPsi n : ℚ) ^ k
            + (sigmaOne n : ℚ) ^ k) +
        (dedekindPsi n : ℚ) ^ k /
          ((n.totient : ℚ) ^ k
            + (sigmaOne n : ℚ) ^ k) +
        (sigmaOne n : ℚ) ^ k /
          ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k) := by sorry
