-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_descend_gen
-- name    : ReciprocityTheory.ChartRestriction.G.Out.TLinPf.descend_gen
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:15:00.397928+00:00
-- url     : https://prove2.me/theorems/032758ed-b209-4741-8332-0bb72fe86b9c
-- title:
--   TLin Pf: descend gen
-- statement:
--   The TLin Pf construction uses the descend gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/DescGen.lean#L11-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/DescGen.lean#L11-L35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_DescGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.TLinPf

theorem ReciprocityTheory.ChartRestriction.G.Out.TLinPf.descend_gen {X Y : Scheme.{0}} (Q : X ⟶ Y) [Flat Q] [Surjective Q] [IsAffineHom Q]
    (ρ : Γ(X, ⊤))
    (hρ : ∀ {Z : Scheme.{0}} (y1 y2 : Z ⟶ X), y1 ≫ Q = y2 ≫ Q → y1.appTop.hom ρ = y2.appTop.hom ρ) :
    ∃ v : Γ(Y, ⊤), Q.appTop.hom v = ρ := by sorry
