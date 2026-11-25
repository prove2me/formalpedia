-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_span_range_eq_of_mul_unit
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.span_range_eq_of_mul_unit
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:40:37.04849+00:00
-- url     : https://prove2.me/theorems/9dfbcb01-4e04-4f3e-87e2-2362476089a4
-- title:
--   Irreducible Component Preimages: span range eq of mul unit
-- statement:
--   The Irreducible Component Preimages construction uses the span range eq of mul unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L230-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L230-L243

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
noncomputable section
variable {W : Scheme.{0}}
variable {s : W ⟶ Spec (.of ℂ)}

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.span_range_eq_of_mul_unit {R : Type*} [CommRing R] {ι : Type*} (u v w : ι → R)
    (hw : ∀ i, IsUnit (w i)) (h : ∀ i, v i * w i = u i) :
    Ideal.span (Set.range u) = Ideal.span (Set.range v) := by sorry
