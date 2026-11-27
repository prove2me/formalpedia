-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_ValUFD_isUnit_mvPolynomial
-- name    : ReciprocityTheory.ChartRestriction.G.T0.ValUFD.isUnit_mvPolynomial
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:14:42.142035+00:00
-- url     : https://prove2.me/theorems/f68d18e0-76ec-44ba-baa2-99c6deb096dc
-- title:
--   Val UFD: is Unit mv Polynomial
-- statement:
--   The Val UFD construction uses the is Unit mv Polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValUFD.lean#L70-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/ValUFD.lean#L70-L73

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

theorem ReciprocityTheory.ChartRestriction.G.T0.ValUFD.isUnit_mvPolynomial {σ K : Type*} [Field K] (κ : MvPolynomial σ K) (h : IsUnit κ) :
    ∃ k : K, k ≠ 0 ∧ κ = MvPolynomial.C k := by sorry
