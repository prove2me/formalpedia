-- Prove2me | Theorems.Thm_P2M_GlobalTheory_T_tauBimult_of_baseChange__cd2ce5c85906
-- name    : P2M_GlobalTheory_T_tauBimult_of_baseChange__cd2ce5c85906
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T16:39:52.152192+00:00
-- url     : https://prove2.me/theorems/b05d0aee-9430-56bd-bbb6-89347adfa02c
-- title:
--   P2 M Global Theory T tau Bimult of base Change  cd2ce5c85906: P2 M Global Theory T tau Bimult of base Change  cd2ce5c85906
-- statement:
--   The P2 M Global Theory T tau Bimult of base Change  cd2ce5c85906 construction uses the P2 M Global Theory T tau Bimult of base Change  cd2ce5c85906 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TauBimultOfBaseChangeStatement.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/TauBimultOfBaseChangeStatement.lean#L17-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TauBimultOfBaseChange
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SecCmp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_TauBimultOfBaseChangeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000

theorem P2M_GlobalTheory_T_tauBimult_of_baseChange__cd2ce5c85906 : GlobalFnsSt → ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D'.TauBimult → D.TauBimult := by sorry

alias «GlobalTheory».«T».«tauBimult_of_baseChange'» := P2M_GlobalTheory_T_tauBimult_of_baseChange__cd2ce5c85906
