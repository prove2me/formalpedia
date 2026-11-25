-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_GtBCPf_isPullback_resLE
-- name    : ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPullback_resLE
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:31:00.750908+00:00
-- url     : https://prove2.me/theorems/64ec2445-9c01-5851-a137-1ad7911c9d9a
-- title:
--   Gt BCPf: is Pullback res LE
-- statement:
--   The Gt BCPf construction uses the is Pullback res LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/Affine.lean#L17-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/BaseChangeKernels/Affine.lean#L17-L31

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

theorem ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPullback_resLE (sq : IsPullback g q' q b) (V : B.Opens) (V' : B'.Opens)
    (hle : V' ≤ b ⁻¹ᵁ V) (hleG : q' ⁻¹ᵁ V' ≤ g ⁻¹ᵁ (q ⁻¹ᵁ V)) :
    IsPullback (g.resLE (q ⁻¹ᵁ V) (q' ⁻¹ᵁ V') hleG) (q'.resLE V' (q' ⁻¹ᵁ V') le_rfl)
      (q.resLE V (q ⁻¹ᵁ V) le_rfl) (b.resLE V V' hle) := by sorry
