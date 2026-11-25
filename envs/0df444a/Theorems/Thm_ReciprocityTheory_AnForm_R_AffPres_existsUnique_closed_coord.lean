-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_AffPres_existsUnique_closed_coord
-- name    : ReciprocityTheory.AnForm.R.AffPres.existsUnique_closed_coord
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:31:58.847696+00:00
-- url     : https://prove2.me/theorems/06d3777d-416b-5806-a5e0-905976a4aacc
-- title:
--   Aff Pres: exists Unique closed coord
-- statement:
--   The Aff Pres construction uses the exists Unique closed coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLoc.lean#L102-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/StalkLoc.lean#L102-L141

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLocB
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory MvPolynomial
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
noncomputable section
variable {W : Scheme.{0}} {s : W ⟶ Spec (.of ℂ)}
open ReciprocityTheory.AnForm.R.AffPres
variable (P : AffPres s)

theorem ReciprocityTheory.AnForm.R.AffPres.existsUnique_closed_coord (p : Fin P.n → ℂ) (hp : ∀ h ∈ P.K, eval p h = 0) :
    ∃! x : W, ∃ hx : x ∈ P.V, IsClosed {x} ∧ P.coord x hx = p := by sorry
