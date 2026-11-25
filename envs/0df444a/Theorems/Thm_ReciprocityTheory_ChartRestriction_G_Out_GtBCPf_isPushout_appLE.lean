-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_isPushout_appLE
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:01.561771+00:00
-- url     : https://prove2.me/theorems/4bdd18ae-1de1-5d29-b93a-8e0ea54f05e6
-- title:
--   Gt BCPf: is Pushout app LE
-- statement:
--   The Gt BCPf construction uses the is Pushout app LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/Affine.lean#L33-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/Affine.lean#L33-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_BaseChangeKernels_Affine
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Out.GtBCPf
universe u
variable {G B G' B' : Scheme.{u}} {g : G' ⟶ G} {q' : G' ⟶ B'} {q : G ⟶ B} {b : B' ⟶ B}

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE (sq : IsPullback g q' q b) (hq : IsAffineHom q) {V : B.Opens}
    (hV : IsAffineOpen V) {V' : B'.Opens} (hV' : IsAffineOpen V')
    (hle : V' ≤ b ⁻¹ᵁ V) (hleG : q' ⁻¹ᵁ V' ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V)) :
    IsPushout (q.app V) (b.appLE V V' hle) (g.appLE (q ⁻¹ᵁ V) (q' ⁻¹ᵁ V') hleG) (q'.app V') := by sorry
