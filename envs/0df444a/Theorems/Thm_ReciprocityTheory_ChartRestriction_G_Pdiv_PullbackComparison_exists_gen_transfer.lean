-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Pdiv_PullbackComparison_exists_gen_transfer
-- name    : ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.exists_gen_transfer
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:18:59.225012+00:00
-- url     : https://prove2.me/theorems/0b808be1-f28e-4242-a251-95d4592ce413
-- title:
--   Pullback Comparison: exists gen transfer
-- statement:
--   The Pullback Comparison construction uses the exists gen transfer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/ExistsGenTransfer.lean#L75-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/PlaceDivisors/SiegelPullbackTransfer/ExistsGenTransfer.lean#L75-L87

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_AdelicGL2ExtOfLocalComponents
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_SiegelPullbackTransfer_ExistsGenTransfer
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
open AlgebraicGeometry CategoryTheory Limits Opposite
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
variable {X Y Z Y' : Scheme.{0}}

theorem ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.exists_gen_transfer {L L' : LB X} (e : L'.ι → L.ι) (hU : ∀ j, L'.U j ≤ L.U (e j))
    (hg : ∀ i j (y : X) (hy : y ∈ L'.U i ⊓ L'.U j),
      gU y hy (L'.g i j) = gU y (⟨hU i hy.1, hU j hy.2⟩ : y ∈ L.U (e i) ⊓ L.U (e j)) (L.g (e i) (e j)))
    (h : ∃ t : LB.Gen L, t.IsGen) : ∃ t' : LB.Gen L', t'.IsGen := by sorry
