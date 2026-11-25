-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ThetaFn_ext_of_valAt__of_isIso_e7119e5be6b9
-- name    : P2M_GlobalTheory_ThetaFn_ext_of_valAt__of_isIso_e7119e5be6b9
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:11:53.974596+00:00
-- url     : https://prove2.me/theorems/4a3d09ff-4c4a-429c-8878-1a3f3c69e602
-- title:
--   P2 M Global Theory Theta Fn ext of val At  of is Iso e7119e5be6b9: P2 M Global Theory Theta Fn ext of val At  of is Iso e7119e5be6b9
-- statement:
--   The P2 M Global Theory Theta Fn ext of val At  of is Iso e7119e5be6b9 construction uses the P2 M Global Theory Theta Fn ext of val At  of is Iso e7119e5be6b9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L78-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L78-L97

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SemicharacterSqEqOneOfSymmetric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter
variable {X Y : Scheme.{0}} (x : Sp ℂ ⟶ X)

theorem P2M_GlobalTheory_ThetaFn_ext_of_valAt__of_isIso_e7119e5be6b9 [IsIso x] {U : X.Opens} {f f' : Γ(X, U)}
    (h : ⊤ ≤ x ⁻¹ᵁ U → valAt' x U f = valAt' x U f') : f = f' := by sorry

alias «GlobalTheory».«ThetaFn».«ext_of_valAt'_of_isIso» := P2M_GlobalTheory_ThetaFn_ext_of_valAt__of_isIso_e7119e5be6b9
