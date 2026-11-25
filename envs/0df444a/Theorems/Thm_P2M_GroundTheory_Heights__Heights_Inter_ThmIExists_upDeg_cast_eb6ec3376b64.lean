-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_upDeg_cast_eb6ec3376b64
-- name    : P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_upDeg_cast_eb6ec3376b64
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:26:51.49453+00:00
-- url     : https://prove2.me/theorems/07c1b323-81a6-43a8-8599-2470f167c86f
-- title:
--   P2 M Ground Theory Heights  Heights Inter Thm IExists up Deg cast eb6ec3376b64: P2 M Ground Theory Heights  Heights Inter Thm IExists up Deg cast eb6ec3376b64
-- statement:
--   The P2 M Ground Theory Heights  Heights Inter Thm IExists up Deg cast eb6ec3376b64 construction uses the P2 M Ground Theory Heights  Heights Inter Thm IExists up Deg cast eb6ec3376b64 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L92-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean#L92-L98

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

theorem P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_upDeg_cast_eb6ec3376b64 (A : HermLine ι) (k : K) : ((upDeg A k : ℕ) : ℤ) = A.a k + shift A := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Inter».«ThmIExists».«upDeg_cast» := P2M_GroundTheory_Heights__Heights_Inter_ThmIExists_upDeg_cast_eb6ec3376b64
