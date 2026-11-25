-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_tu_pull
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.tu_pull
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:11:54.874947+00:00
-- url     : https://prove2.me/theorems/9fa97eef-ded0-5975-acb2-b61c619eaebd
-- title:
--   DVR: tu pull
-- statement:
--   The DVR construction uses the tu pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdIso.lean#L52-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdIso.lean#L52-L60

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

theorem ReciprocityTheory.ChartRestriction.G.DVR.tu_pull (h : Z ⟶ Y) {W : Y.Opens} {V : Z.Opens} (hV : V ≤ h ⁻¹ᵁ W) {ψ : Y ⟶ X} {p : ι}
    (hW : W ≤ ψ ⁻¹ᵁ U p) :
    res hV (pullU h W (tu U u W ψ p)) = tu U u V (h ≫ ψ) p := by sorry
