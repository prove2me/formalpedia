-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_germ_unit_iff
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.germ_unit_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:44:49.971797+00:00
-- url     : https://prove2.me/theorems/7ada2550-865e-5133-8358-f789ad75534c
-- title:
--   Irreducible Component Preimages: germ unit iff
-- statement:
--   The Irreducible Component Preimages construction uses the germ unit iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L213-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L213-L220

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

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.germ_unit_iff (P : AffPres s) (y : W) (hy : y ∈ P.V) (hc : IsClosed ({y} : Set W))
    (g : MvPolynomial (Fin P.n) ℂ) :
    IsUnit (W.presheaf.germ P.V y hy (P.secHom g)) ↔ eval (P.coord y hy) g ≠ 0 := by sorry
