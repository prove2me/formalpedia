-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_log_norm_div_sameOrbit_414d78e5728f
-- name    : P2M_GroundTheory_Heights__Heights_Inter_log_norm_div_sameOrbit_414d78e5728f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:23:40.18395+00:00
-- url     : https://prove2.me/theorems/8068b1e8-56c8-4b8f-a638-662ebb5cae1f
-- title:
--   P2 M Ground Theory Heights  Heights Inter log norm div same Orbit 414d78e5728f: P2 M Ground Theory Heights  Heights Inter log norm div same Orbit 414d78e5728f
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter log norm div same Orbit 414d78e5728f construction uses the P2 M Ground Theory Heights  Heights Inter log norm div same Orbit 414d78e5728f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LogNormDivSameOrbit.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/LogNormDivSameOrbit.lean#L14-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterBridgeB
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogTwoXc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsFurtherLast
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_SameOrbitOneSpecZ
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LogNormDivSameOrbit
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

theorem P2M_GroundTheory_Heights__Heights_Inter_log_norm_div_sameOrbit_414d78e5728f {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a)
    {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖) =
      Real.log (‖eval z' (map (Int.castRingHom ℂ) f)‖ / ‖eval z' (map (Int.castRingHom ℂ) g)‖) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«log_norm_div_sameOrbit» := P2M_GroundTheory_Heights__Heights_Inter_log_norm_div_sameOrbit_414d78e5728f
