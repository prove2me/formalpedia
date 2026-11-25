-- Prove2me | Theorems.Thm_PalomarDimitrov_conjecture3EqualityIffPrime
-- name    : PalomarDimitrov.conjecture3EqualityIffPrime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T08:58:16.802883+00:00
-- url     : https://prove2.me/theorems/225e94b9-72e4-4e81-a6df-291e983aff43
-- title:
--   Palomar Dimitrov: conjecture3 Equality Iff Prime
-- statement:
--   Proved equality characterization for Dimitrov's Conjecture 3.
--
--   Source: https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/Solution.lean#L74-L90
-- source:
--   https://github.com/pro20541/dimitrov-conjectures-lean/blob/95809b59deefd8dfad81e398250aedd7e1aea3b3/Solution.lean#L74-L90

import Definitions.Def_FrontierMathLean_DimitrovConjecture1Equality
import Definitions.Def_FrontierMathLean_DimitrovConjecture3Equality
import Definitions.Def_DimitrovConjectures_Solution
set_option autoImplicit false
open Finset
open scoped ArithmeticFunction.sigma
open PalomarDimitrov

theorem PalomarDimitrov.conjecture3EqualityIffPrime (k n : ℕ) (hk : 1 ≤ k) (hn : 2 ≤ n) :
    (((4 * ((n : ℚ) + 1) ^ (2 * k)
            + (((n : ℚ) ^ 2 - 1) ^ k)
            + ((n : ℚ) - 1) ^ (2 * k)) /
          (2 * (((n : ℚ) + 1) ^ (2 * k)
            + (((n : ℚ) ^ 2 - 1) ^ k))) =
        (n.totient : ℚ) ^ k /
            ((dedekindPsi n : ℚ) ^ k
              + (sigmaOne n : ℚ) ^ k) +
          (dedekindPsi n : ℚ) ^ k /
            ((n.totient : ℚ) ^ k
              + (sigmaOne n : ℚ) ^ k) +
          (sigmaOne n : ℚ) ^ k /
            ((n.totient : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k))) ↔
      n.Prime := by sorry
