-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_Canon_canonGen_corr
-- name    : ReciprocityTheory.ChartRestriction.G.Out.Canon.canonGen_corr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:24:21.280973+00:00
-- url     : https://prove2.me/theorems/d7ae098f-01bb-4a62-87cc-62d022f15cca
-- title:
--   Canon: canon Gen corr
-- statement:
--   The Canon construction uses the canon Gen corr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/CanonGenIsGen.lean#L169-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/CanonGenIsGen.lean#L169-L185

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
variable {K K' : Type} [Fintype K] [Fintype K']
variable (L)
variable {L}

theorem ReciprocityTheory.ChartRestriction.G.Out.Canon.canonGen_corr (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X))
    (ε' : K' → ℤ) (hsub : ∀ k, ∃ k', φ' k' = φ k) (t : LB.Gen (LB.LinComb L φ ε)) :
    LB.Gen.Corr L φ ε φ' ε' t (canonGen L φ ε φ' ε' hsub t) := by sorry
