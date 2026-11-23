-- Prove2me | Theorems.Thm_SPP_measure_le_of_not_prime
-- name    : SPP.measure_le_of_not_prime
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T08:13:19.164796+00:00
-- url     : https://prove2.me/theorems/b0a32e8e-072c-4382-9365-5083686a0ee2
-- title:
--   SPP: measure le of not prime
-- statement:
--   The same in terms of probability.
--
--   Source: https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L697-L718
-- source:
--   https://github.com/hanwenzhu/miller-rabin/blob/9042c23578732ec7a8609ea8a569f58d81614c8c/MillerRabin/StrongProbable.lean#L697-L718

import Mathlib
import Definitions.Def_MillerRabin_Mathlib_Data_Fintype_Units
import Definitions.Def_MillerRabin_Mathlib_Algebra_Group_Subgroup_Lattice
import Definitions.Def_MillerRabin_FermatProbable
import Definitions.Def_MillerRabin_Lemmas
import Definitions.Def_MillerRabin_Val2
import Definitions.Def_MillerRabin_StrongProbable
set_option autoImplicit false
open Nat
open SPP
open Finset
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem SPP.measure_le_of_not_prime {n : ℕ} [hn : Fact (1 < n)] (ho : Odd n) (hnp : ¬n.Prime) :
    (millerRabinRandomSource n).toMeasure {a | SPP n a} ≤ 1 / 4 := by sorry
