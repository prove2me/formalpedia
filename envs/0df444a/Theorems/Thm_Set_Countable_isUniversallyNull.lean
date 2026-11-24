-- Prove2me | Theorems.Thm_Set_Countable_isUniversallyNull
-- name    : Set.Countable.isUniversallyNull
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T07:21:38.576487+00:00
-- url     : https://prove2.me/theorems/cfa2ce3c-f87a-4168-930a-ccc69a20c560
-- title:
--   Countable: is Universally Null
-- statement:
--   The Countable construction uses the is Universally Null property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/UniversallyNull.lean#L52-L53
-- source:
--   https://github.com/VictorLiwentao/open-logic-24-add-un/blob/a4fe8608ded270fd55615fc649a111b46eeaa607/AddUN/UniversallyNull.lean#L52-L53

module
public import Definitions.Def_AddUN_IdealInvariant
public import Mathlib.MeasureTheory.MeasurableSpace.Card
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProductMeasure
public import Definitions.Def_AddUN_UniversallyNull
set_option autoImplicit false
@[expose] public section
public section
open Set Filter Topology Cardinal IdealInvariant
open scoped ENNReal
open MeasureTheory
variable {X : Type*} [MeasurableSpace X] {A B : Set X}

theorem Set.Countable.isUniversallyNull (hA : A.Countable) : IsUniversallyNull A := by sorry
