-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_secHom_surjective
-- name    : ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.secHom_surjective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:38:40.182916+00:00
-- url     : https://prove2.me/theorems/5cbfc3f8-85e8-5513-af2e-c81a06a84fcd
-- title:
--   Irreducible Component Preimages: sec Hom surjective
-- statement:
--   The Irreducible Component Preimages construction uses the sec Hom surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L190-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/ExistsMulMemOfAlgebraMapLocRingEqZero.lean#L190-L195

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

theorem ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.secHom_surjective (P : AffPres s) : Function.Surjective P.secHom := by sorry
