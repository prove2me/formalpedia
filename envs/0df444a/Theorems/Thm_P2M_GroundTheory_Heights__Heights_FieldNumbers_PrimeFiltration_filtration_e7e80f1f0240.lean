-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_filtration_e7e80f1f0240
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_filtration_e7e80f1f0240
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:17:27.036888+00:00
-- url     : https://prove2.me/theorems/8d4d1b00-e69e-423e-81fa-fef94ccab21e
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration filtration e7e80f1f0240: P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration filtration e7e80f1f0240
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration filtration e7e80f1f0240 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Prime Filtration filtration e7e80f1f0240 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L395-L449
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean#L395-L449

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PrimeFiltration
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]
open Classical

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_filtration_e7e80f1f0240 (h1 : HilbExactDivide.Statement.{u}) (J : Ideal (MRing ι F))
    (hJ : IsMultiHomogIdeal J) :
    ∃ (r : ℕ) (Q : Fin r → Ideal (MRing ι F)) (c : Fin r → K → ℕ),
      (∀ j, (Q j).IsPrime ∧ IsMultiHomogIdeal (Q j) ∧ J ≤ Q j) ∧
      (∀ m, hilbFn J m = ∑ j, hilbFn (Q j) (m - fun k => (c j k : ℤ))) ∧
      (∀ W (hW : W ∈ J.minimalPrimes),
        haveI : W.IsPrime := hW.1.1
        (((∑ j, if Q j = W then 1 else 0 : ℕ)) : ℕ∞) = multAt J W) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«PrimeFiltration».«filtration» := P2M_GroundTheory_Heights__Heights_FieldNumbers_PrimeFiltration_filtration_e7e80f1f0240
