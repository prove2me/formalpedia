-- Prove2me | Theorems.Thm_P2M_GlobalTheory_bijective___appLE_4ffb2aed58ba
-- name    : P2M_GlobalTheory_bijective___appLE_4ffb2aed58ba
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:45:02.852094+00:00
-- url     : https://prove2.me/theorems/fdc4f56c-d873-4fd8-acc3-bf5cd7eef5a5
-- title:
--   P2 M Global Theory bijective   app LE 4ffb2aed58ba: P2 M Global Theory bijective   app LE 4ffb2aed58ba
-- statement:
--   The P2 M Global Theory bijective   app LE 4ffb2aed58ba construction uses the P2 M Global Theory bijective   app LE 4ffb2aed58ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L573-L576
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean#L573-L576

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y : Scheme.{0}}

theorem P2M_GlobalTheory_bijective___appLE_4ffb2aed58ba (W : X.Opens) {V : X.Opens} (hV : V ≤ W) {T : W.toScheme.Opens}
    (h : T = W.ι ⁻¹ᵁ V) : Function.Bijective (W.ι.appLE V T h.le).hom := by sorry

alias «GlobalTheory».«bijective_ι_appLE» := P2M_GlobalTheory_bijective___appLE_4ffb2aed58ba
