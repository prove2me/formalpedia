-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ThetaFn_valAt__unit_zpow_a99706afe68e
-- name    : P2M_GlobalTheory_ThetaFn_valAt__unit_zpow_a99706afe68e
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:12:08.419123+00:00
-- url     : https://prove2.me/theorems/401b737e-9122-4f00-9905-3a8cc675f0d0
-- title:
--   P2 M Global Theory Theta Fn val At  unit zpow a99706afe68e: P2 M Global Theory Theta Fn val At  unit zpow a99706afe68e
-- statement:
--   The P2 M Global Theory Theta Fn val At  unit zpow a99706afe68e construction uses the P2 M Global Theory Theta Fn val At  unit zpow a99706afe68e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L42-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ExistsUniqueSecIsFnAt.lean#L42-L47

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

theorem P2M_GlobalTheory_ThetaFn_valAt__unit_zpow_a99706afe68e {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)ˣ) (k : ℤ) :
    valAt' x U (f ^ k).val = valAt' x U f.val ^ k := by sorry

alias «GlobalTheory».«ThetaFn».«valAt'_unit_zpow» := P2M_GlobalTheory_ThetaFn_valAt__unit_zpow_a99706afe68e
