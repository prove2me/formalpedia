-- Prove2me | Theorems.Thm_ReciprocityTheory_AnForm_R_ds_local
-- name    : ReciprocityTheory.AnForm.R.ds_local
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:37:00.864262+00:00
-- url     : https://prove2.me/theorems/1ee8fb50-62c8-5ae1-b4d2-57441e3247de
-- title:
--   R: ds local
-- statement:
--   The R construction uses the ds local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheafA.lean#L282-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/AnalyticForms/RegularLocalRings/DivSheafA.lean#L282-L318

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
variable {W : Scheme.{u}} {ι' : Type*} {V : ι' → W.Opens} {g : ∀ c, Γ(W, V c)}

theorem ReciprocityTheory.AnForm.R.ds_local (hg : ∀ c c' (x : W) (hx : x ∈ V c) (hx' : x ∈ V c'), ∃ u : (W.presheaf.stalk x)ˣ,
      W.presheaf.germ (V c) x hx (g c) = u * W.presheaf.germ (V c') x hx' (g c'))
    {U : W.affineOpens} (s a : Γ(W, U))
    (ha : ∀ z (hz : z ∈ U.1), z ∈ W.basicOpen s → W.presheaf.germ U.1 z hz a ∈ dsK V g z)
    (c : ι') (t : Γ(W, U)) (htc : W.basicOpen t ≤ V c) :
    ∃ m : ℕ, ∀ z (hz : z ∈ W.basicOpen t),
      W.presheaf.germ U.1 z (W.basicOpen_le t hz) (s ^ m * a) ∈ dsK V g z := by sorry
