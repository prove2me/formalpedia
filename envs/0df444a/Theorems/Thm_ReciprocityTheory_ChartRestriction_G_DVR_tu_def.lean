-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tu_def
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.tu_def
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:43.460875+00:00
-- url     : https://prove2.me/theorems/489ff576-e82e-4561-ad15-b627e6ea43b5
-- title:
--   DVR: tu def
-- statement:
--   The DVR construction uses the tu def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdIso.lean#L23-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdIso.lean#L23-L26

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y Z : Scheme.{0}} {ι : Type} (U : ι → X.Opens) (u : ∀ p, Γ(X, U p)ˣ)
variable {U u}

theorem ReciprocityTheory.ChartRestriction.G.DVR.tu_def {V : Y.Opens} {ψ : Y ⟶ X} {p : ι} (h : V ≤ ψ ⁻¹ᵁ U p) :
    tu U u V ψ p = res h (pullU ψ _ (u p)) := by sorry
