-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_Canon_gW_self
-- name    : ReciprocityTheory.ChartRestriction.G.Out.Canon.gW_self
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:47:19.69671+00:00
-- url     : https://prove2.me/theorems/25c1c1b8-1f68-4418-897d-a6d5107f7293
-- title:
--   Canon: g W self
-- statement:
--   The Canon construction uses the g W self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/CanonGenIsGen.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/CanonGenIsGen.lean#L56-L60

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_CanonGenIsGen
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
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out.Canon
variable {X Y : Scheme.{0}} (L : LB X)
variable {L}

theorem ReciprocityTheory.ChartRestriction.G.Out.Canon.gW_self (hL : L.IsLB) {W : Y.Opens} (ψ : Y ⟶ X) (a : L.ι)
    (h : W ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U a)) : gW L ψ a a h = 1 := by sorry
