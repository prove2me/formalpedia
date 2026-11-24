-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_finrank_eq_beef6e4ea699
-- name    : P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_finrank_eq_beef6e4ea699
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:35.975099+00:00
-- url     : https://prove2.me/theorems/9bc25c14-b54c-4fef-b462-d6e17cdeb1f6
-- title:
--   P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide finrank eq beef6e4ea699: P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide finrank eq beef6e4ea699
-- statement:
--   The P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide finrank eq beef6e4ea699 construction uses the P2 M Ground Theory Heights  Heights Field Numbers Hilb Exact Divide finrank eq beef6e4ea699 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbExactDivide.lean#L62-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PHilbExactDivide.lean#L62-L150

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PGradedFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PHilbExactDivide
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
open GroundTheory.Heights₂.Heights.FieldNumbers.HilbExactDivide
variable {K : Type} [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical

theorem P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_finrank_eq_beef6e4ea699 (h1 : GradedFinite.Statement.{u}) [Fintype K] [∀ k, Fintype (ι k)]
    {I : Ideal (MRing ι F)} (hI : IsMultiHomogIdeal I) {c : K → ℕ} {s : MRing ι F}
    (hs : IsMultiHomog s c) (n : K → ℕ) :
    Module.finrank F (gradedPiece I n) =
      Module.finrank F (gradedPiece (I ⊔ Ideal.span {s}) n) +
        (if c ≤ n then Module.finrank F (gradedPiece (I.colon (Ideal.span {s})) (n - c))
          else 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FieldNumbers».«HilbExactDivide».«finrank_eq» := P2M_GroundTheory_Heights__Heights_FieldNumbers_HilbExactDivide_finrank_eq_beef6e4ea699
