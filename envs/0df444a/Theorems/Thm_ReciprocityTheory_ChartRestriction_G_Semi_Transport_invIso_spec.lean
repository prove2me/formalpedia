-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_Transport_invIso_spec
-- name    : ReciprocityTheory.ChartRestriction.G.Semi.Transport.invIso_spec
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T10:35:13.646549+00:00
-- url     : https://prove2.me/theorems/ed894a3e-cb4b-5582-ae7b-fe8b2f07b4f3
-- title:
--   Transport: inv Iso spec
-- statement:
--   The Transport construction uses the inv Iso spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/Transport.lean#L203-L216
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/UniformBaseChange/Transport.lean#L203-L216

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_gU_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_unit_ext

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Transport
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (gU unit_ext gU_res)
variable {X : Scheme.{0}}
variable {A B C : LB X}

theorem ReciprocityTheory.ChartRestriction.G.Semi.Transport.invIso_spec (hA : A.IsLB) (hB : B.IsLB) (w : LB.Iso A B) (hw : w.IsGen) :
    (invIso w).IsGen ∧ ∀ (a : LB.Gen A) (b : LB.Gen B), LB.Gen.Maps w a b →
      LB.Gen.Maps (invIso w) b a := by sorry
