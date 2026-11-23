-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_linCombIso_isGen
-- name    : ReciprocityTheory.ChartRestriction.G.DVR.linCombIso_isGen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:46:04.262895+00:00
-- url     : https://prove2.me/theorems/a3314cb4-cd73-4faf-87ce-44f7d61e8367
-- title:
--   DVR: lin Comb Iso is Gen
-- statement:
--   The DVR construction uses the lin Comb Iso is Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdIso.lean#L160-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/DiscreteValuationRings/ProdIso.lean#L160-L194

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
variable {X Y : Scheme.{0}} {L M : LB X}

theorem ReciprocityTheory.ChartRestriction.G.DVR.linCombIso_isGen (w : LB.Iso L M) (hw : w.IsGen) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) : (LB.linCombIso w φ ε).IsGen := by sorry
