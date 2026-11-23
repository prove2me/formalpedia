-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_mem_dsJ
-- name    : ReciprocityTheory.AnForm.R.mem_dsJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:34.640443+00:00
-- url     : https://prove2.me/theorems/5bdb067e-5e40-429c-9752-b0461720ad22
-- title:
--   R: mem ds J
-- statement:
--   The R construction uses the mem ds J property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheafA.lean#L216-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheafA.lean#L216-L220

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
variable {W : Scheme.{u}} {ι' : Type*} (V : ι' → W.Opens) (g : ∀ c, Γ(W, V c))
variable {V g}
variable (V g)
variable {V g}

theorem ReciprocityTheory.AnForm.R.mem_dsJ {U : W.affineOpens} {f : Γ(W, U)} :
    f ∈ dsJ V g U ↔ ∀ x (hx : x ∈ U.1), W.presheaf.germ U.1 x hx f ∈ dsK V g x := by sorry
