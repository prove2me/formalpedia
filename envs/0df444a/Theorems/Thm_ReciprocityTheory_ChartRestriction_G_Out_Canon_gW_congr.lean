-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_Canon_gW_congr
-- name    : ReciprocityTheory.ChartRestriction.G.Out.Canon.gW_congr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:47:36.271593+00:00
-- url     : https://prove2.me/theorems/318bfb6b-f264-4909-b8e0-a31f447fc136
-- title:
--   Canon: g W congr
-- statement:
--   The Canon construction uses the g W congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/CanonGenIsGen.lean#L47-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/CanonGenIsGen.lean#L47-L50

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

theorem ReciprocityTheory.ChartRestriction.G.Out.Canon.gW_congr {W : Y.Opens} {ψ ψ' : Y ⟶ X} {a a' b b' : L.ι} (hψ : ψ = ψ') (ha : a = a')
    (hb : b = b') (h : W ≤ ψ ⁻¹ᵁ (L.U a ⊓ L.U b)) (h' : W ≤ ψ' ⁻¹ᵁ (L.U a' ⊓ L.U b')) :
    gW L ψ a b h = gW L ψ' a' b' h' := by sorry
