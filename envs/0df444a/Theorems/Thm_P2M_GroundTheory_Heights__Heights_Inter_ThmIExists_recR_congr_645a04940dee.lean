-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_recR_congr_645a04940dee
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_recR_congr_645a04940dee
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T04:02:53.409677+00:00
-- url     : https://prove2.me/theorems/7f810b13-75b6-4185-890a-dca983b304ee
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists rec R congr 645a04940dee: P2 M Ground Theory Heights  Heights Inter Thm IExists rec R congr 645a04940dee
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists rec R congr 645a04940dee construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists rec R congr 645a04940dee property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L118-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L118-L122

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_recR_congr_645a04940dee {I J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {n : ℕ}
    (h : ∀ W L, I W n L = J W n L) (P : Ideal (MRing ι)) (L : Fin n → HermLine ι) (A : HermLine ι)
    (s : MRing ι) : recR I P L A s = recR J P L A s := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«recR_congr» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_recR_congr_645a04940dee
