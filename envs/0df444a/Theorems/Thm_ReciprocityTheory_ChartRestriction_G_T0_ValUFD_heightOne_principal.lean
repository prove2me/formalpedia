-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_heightOne_principal
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValUFD.heightOne_principal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:50:51.856884+00:00
-- url     : https://prove2.me/theorems/b311bd08-c7dd-4539-a7c0-edca72ed7145
-- title:
--   Val UFD: height One principal
-- statement:
--   The Val UFD construction uses the height One principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValUFD.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValUFD.lean#L10-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValUFD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open ReciprocityTheory.ChartRestriction.G.T0.ValUFD
variable {R F : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] [Field F]
  [Algebra R F] [IsFractionRing R F]

theorem ReciprocityTheory.ChartRestriction.G.T0.ValUFD.heightOne_principal (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    ∃ g : R, Prime g ∧ p = Ideal.span {g} := by sorry
