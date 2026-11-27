-- Prove2me | Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_SatakeVectors_contId_ne_bot
-- name    : ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.contId_ne_bot
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:27:51.857374+00:00
-- url     : https://prove2.me/theorems/6a048fdc-7a14-53b1-8fcd-3a367849734d
-- title:
--   Satake Vectors: cont Id ne bot
-- statement:
--   The Satake Vectors construction uses the cont Id ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussAbsMulSupportFinite.lean#L183-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussAbsMulSupportFinite.lean#L183-L187

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Qdist
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_SemistableReduction_GaussAbsMulOfMonomialOrder
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegCA
import Mathlib.NumberTheory.Height.NumberField
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]

theorem ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.contId_ne_bot {κ : Type*} (G₀ : MvPolynomial κ (𝓞 K)) (h : G₀ ≠ 0) : contId G₀ ≠ ⊥ := by sorry
