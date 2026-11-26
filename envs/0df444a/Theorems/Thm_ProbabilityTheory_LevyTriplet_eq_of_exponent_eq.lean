-- Prove2me | Theorems.Thm_ProbabilityTheory_LevyTriplet_eq_of_exponent_eq
-- name    : ProbabilityTheory.LevyTriplet.eq_of_exponent_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T23:31:10.568913+00:00
-- url     : https://prove2.me/theorems/4b3eccba-2bba-5441-bd6b-901726914c03
-- title:
--   Uniqueness of the Lévy triplet from its exponent
-- statement:
--   Two real Lévy triplets with equal characteristic exponents are equal, using the fixed truncation convention.
-- source:
--   StochLean.Probability.InfinitelyDivisible.LevyKhintchine

import Definitions.Def_SourceProof_1a692c64413256141ec63577

open ProbabilityTheory Filter MeasureTheory
open scoped ENNReal NNReal Topology

theorem ProbabilityTheory.LevyTriplet.eq_of_exponent_eq {η ξ : LevyTriplet} (h : η.exponent = ξ.exponent) : η = ξ := by sorry
