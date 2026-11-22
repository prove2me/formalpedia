-- Prove2me | Theorems.Thm_P2M_pi_pi__7f25e995c05a
-- name    : P2M_pi_pi__7f25e995c05a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T08:34:45.438558+00:00
-- url     : https://prove2.me/theorems/731b0999-0547-4bde-ae1a-ffcb4beada5f
-- title:
--   P2 M pi pi  7f25e995c05a: P2 M pi pi  7f25e995c05a
-- statement:
--   The P2 M pi pi  7f25e995c05a construction uses the P2 M pi pi  7f25e995c05a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L81-L86
-- source:
--   https://github.com/b-mehta/Polychromatic/blob/418967fa27405f92343e1e1c98c268793d90f914/Polychromatic/ForMathlib/Misc.lean#L81-L86

import Mathlib.Order.Partition.Equipartition
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.UniformOn
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.GCDMonoid.Nat
import Definitions.Def_Polychromatic_ForMathlib_Misc
set_option autoImplicit true
open Finset
open MeasureTheory Measure ProbabilityTheory
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω] {P : ι → Measure Ω}
variable [∀ i, IsProbabilityMeasure (P i)] {s : Set ι}
open Classical

theorem P2M_pi_pi__7f25e995c05a {f : ι → Set Ω} {s : Finset ι} :
    (Measure.pi P) ((s : Set ι).pi f) = ∏ i ∈ s, P i (f i) := by sorry

alias «pi_pi'» := P2M_pi_pi__7f25e995c05a
