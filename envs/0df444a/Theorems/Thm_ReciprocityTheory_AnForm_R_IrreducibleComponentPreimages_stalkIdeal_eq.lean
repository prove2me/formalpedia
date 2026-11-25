-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_stalkIdeal_eq
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.stalkIdeal_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:39:42.05474+00:00
-- url     : https://prove2.me/theorems/e7e73dc1-3853-4799-9b31-e83d384f9ddf
-- title:
--   Irreducible Component Preimages: stalk Ideal eq
-- statement:
--   The Irreducible Component Preimages construction uses the stalk Ideal eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L71-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L71-L93

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

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.stalkIdeal_eq (Z : W.IdealSheafData) (U V : W.affineOpens) (x : W) (hU : x ∈ U.1)
    (hV : x ∈ V.1) : (Z.ideal V).map (W.presheaf.germ V.1 x hV).hom =
      (Z.ideal U).map (W.presheaf.germ U.1 x hU).hom := by sorry
