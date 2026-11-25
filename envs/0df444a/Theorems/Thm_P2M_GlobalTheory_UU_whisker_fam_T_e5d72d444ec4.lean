-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UU_whisker_fam_T_e5d72d444ec4
-- name    : P2M_GlobalTheory_UU_whisker_fam_T_e5d72d444ec4
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:31:54.665187+00:00
-- url     : https://prove2.me/theorems/af0a2eb5-e2e4-571b-abac-0aeb582ba128
-- title:
--   P2 M Global Theory UU whisker fam T e5d72d444ec4: P2 M Global Theory UU whisker fam T e5d72d444ec4
-- statement:
--   The P2 M Global Theory UU whisker fam T e5d72d444ec4 construction uses the P2 M Global Theory UU whisker fam T e5d72d444ec4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsPullSecSval.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsPullSecSval.lean#L30-L44

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsPullSecSval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory GlobalTheory.UU

theorem P2M_GlobalTheory_UU_whisker_fam_T_e5d72d444ec4 {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T T' : Over (Spec (CommRingCat.of R))}
    (ρ : T' ⟶ T) (α : D.X) (i : Fin 4) : (ρ ▷ D.P.A).left ≫ famφT D T α i = famφT D T' α i := by sorry

alias «GlobalTheory».«UU».«whisker_famφT» := P2M_GlobalTheory_UU_whisker_fam_T_e5d72d444ec4
