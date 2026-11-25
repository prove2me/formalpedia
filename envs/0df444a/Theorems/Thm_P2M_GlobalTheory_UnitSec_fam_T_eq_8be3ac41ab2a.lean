-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UnitSec_fam_T_eq_8be3ac41ab2a
-- name    : P2M_GlobalTheory_UnitSec_fam_T_eq_8be3ac41ab2a
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:47:55.457034+00:00
-- url     : https://prove2.me/theorems/c872e229-fa93-59df-bc09-530c875ea998
-- title:
--   P2 M Global Theory Unit Sec fam T eq 8be3ac41ab2a: P2 M Global Theory Unit Sec fam T eq 8be3ac41ab2a
-- statement:
--   The P2 M Global Theory Unit Sec fam T eq 8be3ac41ab2a construction uses the P2 M Global Theory Unit Sec fam T eq 8be3ac41ab2a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/MatchingSectionsExist.lean#L52-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/MatchingSectionsExist.lean#L52-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_MatchingSectionsExist
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UnitSec

theorem P2M_GlobalTheory_UnitSec_fam_T_eq_8be3ac41ab2a {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (α : D.X) (k : Fin 4) : famφT D T α k = (snd T D.P.A).left ≫ D.famφB α k := by sorry

alias «GlobalTheory».«UnitSec».«famφT_eq» := P2M_GlobalTheory_UnitSec_fam_T_eq_8be3ac41ab2a
