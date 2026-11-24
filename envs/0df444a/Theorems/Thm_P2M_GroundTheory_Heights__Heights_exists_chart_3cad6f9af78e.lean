-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_chart_3cad6f9af78e
-- name    : P2M_GroundTheory_Heights__Heights_exists_chart_3cad6f9af78e
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:53:29.16575+00:00
-- url     : https://prove2.me/theorems/d05fcc85-4985-4850-9fde-de314dfd8a93
-- title:
--   P2 M Ground Theory Heights  Heights exists chart 3cad6f9af78e: P2 M Ground Theory Heights  Heights exists chart 3cad6f9af78e
-- statement:
--   The P2 M Ground Theory Heights  Heights exists chart 3cad6f9af78e construction uses the P2 M Ground Theory Heights  Heights exists chart 3cad6f9af78e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L225-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightComparison/HeightObjects.lean#L225-L227

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι] [DecidableEq ι]

theorem P2M_GroundTheory_Heights__Heights_exists_chart_3cad6f9af78e {F : Type*} [Zero F] {x : Cone n F} (hx : BlockNonzero x) :
    ∃ c : (k : ι) → Fin (n k + 1), ∀ k, x k (c k) ≠ 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«exists_chart» := P2M_GroundTheory_Heights__Heights_exists_chart_3cad6f9af78e
