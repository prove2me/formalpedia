-- Prove2me | Theorems.Thm_P2M_GlobalTheory_UU_ToChart_cub_alg__dec35e250081
-- name    : P2M_GlobalTheory_UU_ToChart_cub_alg__dec35e250081
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:48:39.786463+00:00
-- url     : https://prove2.me/theorems/fe675884-1bf5-4ab1-ab46-b96f1d3feda9
-- title:
--   P2 M Global Theory UU To Chart cub alg  dec35e250081: P2 M Global Theory UU To Chart cub alg  dec35e250081
-- statement:
--   The P2 M Global Theory UU To Chart cub alg  dec35e250081 construction uses the P2 M Global Theory UU To Chart cub alg  dec35e250081 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GmResPull.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/GmResPull.lean#L25-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmResPull
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
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.ToChart

theorem P2M_GlobalTheory_UU_ToChart_cub_alg__dec35e250081 {M : Type} [CommGroup M] {C C' a b c d e g h k : M} (H : C * b * c * d * k = a * e * g * h * C') :
    C = a * b⁻¹ * c⁻¹ * d⁻¹ * e * g * h * k⁻¹ * C' := by sorry

alias «GlobalTheory».«UU».«ToChart».«cub_alg'» := P2M_GlobalTheory_UU_ToChart_cub_alg__dec35e250081
