-- Prove2me | Theorems.Thm_P2M_GlobalTheory_ZM_TBase_complex___c5e8033a0765
-- name    : P2M_GlobalTheory_ZM_TBase_complex___c5e8033a0765
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:07:05.776816+00:00
-- url     : https://prove2.me/theorems/8e17df5a-e506-5ab7-bf18-cf65f9b3a794
-- title:
--   P2 M Global Theory ZM TBase complex   c5e8033a0765: P2 M Global Theory ZM TBase complex   c5e8033a0765
-- statement:
--   The P2 M Global Theory ZM TBase complex   c5e8033a0765 construction uses the P2 M Global Theory ZM TBase complex   c5e8033a0765 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/GoodClass.lean#L118-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/GoodClass.lean#L118-L119

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_GoodClass
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.ZM
variable {o : Type} [CommRing o] {S S' : Scheme.{0}}
attribute [instance] TObj.grp
variable {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}

theorem P2M_GlobalTheory_ZM_TBase_complex___c5e8033a0765 (k : ℕ) (hk : k ≠ 0) :
    ((TBase.complex k hk).ζ : ℂ) = Complex.exp (2 * Real.pi * Complex.I / k) := by sorry

alias «GlobalTheory».«ZM».«TBase».«complex_ζ» := P2M_GlobalTheory_ZM_TBase_complex___c5e8033a0765
