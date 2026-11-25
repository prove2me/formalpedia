-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_finsum_hor_eq_c421a4deb190
-- name    : P2M_GroundTheory_Heights__Heights_Inter_finsum_hor_eq_c421a4deb190
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:24:29.343599+00:00
-- url     : https://prove2.me/theorems/5022d8fa-f130-4b06-aa77-f31ac13d8f16
-- title:
--   P2 M Ground Theory Heights  Heights Inter finsum hor eq c421a4deb190: P2 M Ground Theory Heights  Heights Inter finsum hor eq c421a4deb190
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter finsum hor eq c421a4deb190 construction uses the P2 M Ground Theory Heights  Heights Inter finsum hor eq c421a4deb190 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L149-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/NotLtLtOfMemMinimalPrimes.lean#L149-L155

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
open Classical

theorem P2M_GroundTheory_Heights__Heights_Inter_finsum_hor_eq_c421a4deb190 (P : Ideal (MRing ι)) (s : MRing ι) (g : Ideal (MRing ι) → ℝ) :
    (∑ᶠ (W) (_ : W ∈ divSupp P s ∧ IsHorizontal W), g W) =
      ∑ᶠ W ∈ divSupp P s, (if IsHorizontal W then g W else 0) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«finsum_hor_eq» := P2M_GroundTheory_Heights__Heights_Inter_finsum_hor_eq_c421a4deb190
