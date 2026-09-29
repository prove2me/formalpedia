-- Prove2me | Theorems.Thm_Rat_ringOfIntegers_pos_iff_all_real_embeddings
-- name    : Rat.ringOfIntegers_pos_iff_all_real_embeddings
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T22:48:30.588967+00:00
-- url     : https://prove2.me/theorems/509199ba-853e-4ccc-8636-810099ebd39c
-- title:
--   Positivity in the narrow ray condition over the rationals
-- statement:
--   For an algebraic integer $a$ of $\mathbb Q$, positivity under every real embedding of $\mathbb Q$ is equivalent to positivity of the corresponding integer in $\mathbb Z$. This converts the archimedean condition in the narrow ray subgroup of $\mathbb Q$ into the usual positive-generator condition used to identify its ray classes with $(\mathbb Z/n\mathbb Z)^\times$.
-- source:
--   Mathlib, NumberTheory/NumberField/Basic, Rat.ringOfIntegersEquiv and Rat.ringOfIntegersEquiv_apply_coe, https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Basic.html ; Prove2Me Definitions.Def_NarrowRayClassGroup, definition Deep.NTSupply.narrowRaySet, archimedean positivity conjunct.

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.Real.Basic

theorem Rat.ringOfIntegers_pos_iff_all_real_embeddings (a : NumberField.RingOfIntegers ℚ) :
    0 < Rat.ringOfIntegersEquiv a ↔
      ∀ τ : ℚ →+* ℝ, 0 < τ (algebraMap (NumberField.RingOfIntegers ℚ) ℚ a) := by sorry
