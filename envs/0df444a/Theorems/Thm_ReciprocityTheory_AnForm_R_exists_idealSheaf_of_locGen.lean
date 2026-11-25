-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_exists_idealSheaf_of_locGen
-- name    : ReciprocityTheory.AnForm.R.exists_idealSheaf_of_locGen
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T09:37:14.436524+00:00
-- url     : https://prove2.me/theorems/2adf57be-12b8-51dc-b987-709d994eb85b
-- title:
--   R: exists ideal Sheaf of loc Gen
-- statement:
--   The R construction uses the exists ideal Sheaf of loc Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheaf.lean#L97-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheaf.lean#L97-L123

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
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

theorem ReciprocityTheory.AnForm.R.exists_idealSheaf_of_locGen {W : Scheme.{0}} {ι' : Type} (V : ι' → W.Opens)
    (hV : ∀ x : W, ∃ c, x ∈ V c) (g : ∀ c, Γ(W, V c))
    (hg : ∀ c c' (x : W) (hx : x ∈ V c) (hx' : x ∈ V c'), ∃ u : (W.presheaf.stalk x)ˣ,
      W.presheaf.germ (V c) x hx (g c) = u * W.presheaf.germ (V c') x hx' (g c')) :
    ∃ G : W.IdealSheafData, ∀ c (x : W) (hx : x ∈ V c),
      FinalTheorems.stalkId G x = Ideal.span {W.presheaf.germ (V c) x hx (g c)} := by sorry
