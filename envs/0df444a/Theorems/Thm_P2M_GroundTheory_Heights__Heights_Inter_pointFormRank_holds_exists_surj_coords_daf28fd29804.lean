-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormRank_holds_exists_surj_coords_daf28fd29804
-- name    : P2M_GroundTheory_Heights__Heights_Inter_pointFormRank_holds_exists_surj_coords_daf28fd29804
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:24:59.846331+00:00
-- url     : https://prove2.me/theorems/9f9ff078-1e7a-4d2b-a1de-7ed53ac82008
-- title:
--   P2 M Ground Theory Heights  Heights Inter point Form Rank holds exists surj coords daf28fd29804: P2 M Ground Theory Heights  Heights Inter point Form Rank holds exists surj coords daf28fd29804
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter point Form Rank holds exists surj coords daf28fd29804 construction uses the P2 M Ground Theory Heights  Heights Inter point Form Rank holds exists surj coords daf28fd29804 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/EqZeroOfEventuallyEval.lean#L12-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/EqZeroOfEventuallyEval.lean#L12-L42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMapAlt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRatioAlgDep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_EqZeroOfEventuallyEval
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

theorem P2M_GroundTheory_Heights__Heights_Inter_pointFormRank_holds_exists_surj_coords_daf28fd29804 {σ : Type*} {n : ℕ} (ℓ : σ → (Fin n → ℂ) →ₗ[ℂ] ℂ)
    (hℓ : ∀ x, (∀ s, ℓ s x = 0) → x = 0) :
    ∀ m, m ≤ n → ∃ q : Fin m → σ, Function.Surjective (fun x : Fin n → ℂ => fun j => ℓ (q j) x) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«pointFormRank_holds».«exists_surj_coords» := P2M_GroundTheory_Heights__Heights_Inter_pointFormRank_holds_exists_surj_coords_daf28fd29804
