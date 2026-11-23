-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_dsK_eq
-- name    : ReciprocityTheory.AnForm.R.dsK_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:57.773655+00:00
-- url     : https://prove2.me/theorems/00c515a4-8090-47b6-8491-42999a8b72c5
-- title:
--   R: ds K eq
-- statement:
--   The R construction uses the ds K eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheafA.lean#L197-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheafA.lean#L197-L207

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

theorem ReciprocityTheory.AnForm.R.dsK_eq (hg : ∀ c c' (x : W) (hx : x ∈ V c) (hx' : x ∈ V c'), ∃ u : (W.presheaf.stalk x)ˣ,
      W.presheaf.germ (V c) x hx (g c) = u * W.presheaf.germ (V c') x hx' (g c'))
    {x : W} (c) (hc : x ∈ V c) :
    dsK V g x = Ideal.span {W.presheaf.germ (V c) x hc (g c)} := by sorry
