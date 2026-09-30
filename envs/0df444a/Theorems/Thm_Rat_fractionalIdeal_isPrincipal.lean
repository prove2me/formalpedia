-- Prove2me | Theorems.Thm_Rat_fractionalIdeal_isPrincipal
-- name    : Rat.fractionalIdeal_isPrincipal
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T23:10:33.934838+00:00
-- url     : https://prove2.me/theorems/cc5f9636-e226-4bc6-87d4-d015d29e7069
-- title:
--   Every fractional ideal of Q is principal
-- statement:
--   Every nonzero fractional ideal of $\mathcal O_{\mathbb Q}$ is principal. Via $\mathcal O_{\mathbb Q}\cong\mathbb Z$, this is the principal ideal property of the integers, now stated in the fractional-ideal type used by the narrow ray class group. It supplies the principal generator needed to compare ideals with residue classes modulo a rational modulus.
-- source:
--   Mathlib, RingTheory/ClassGroup/Basic, ClassGroup.mulEquiv, ClassGroup.card_classGroup_eq_one, and ClassGroup.mk_eq_one_iff, https://leanprover-community.github.io/mathlib4_docs/Mathlib/RingTheory/ClassGroup/Basic.html ; Mathlib, NumberTheory/NumberField/Basic, Rat.ringOfIntegersEquiv, https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/NumberField/Basic.html .

import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.ClassGroup.Basic

open NumberField nonZeroDivisors

theorem Rat.fractionalIdeal_isPrincipal
    (I : (FractionalIdeal ((NumberField.RingOfIntegers ℚ)⁰) ℚ)ˣ) :
    ((I : FractionalIdeal ((NumberField.RingOfIntegers ℚ)⁰) ℚ) :
      Submodule (NumberField.RingOfIntegers ℚ) ℚ).IsPrincipal := by sorry
