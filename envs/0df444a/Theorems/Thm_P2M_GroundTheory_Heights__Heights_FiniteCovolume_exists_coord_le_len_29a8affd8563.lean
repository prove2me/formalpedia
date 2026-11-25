-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_coord_le_len_29a8affd8563
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_coord_le_len_29a8affd8563
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:40:32.8558+00:00
-- url     : https://prove2.me/theorems/727c3123-e915-494c-81ea-ee15cfffbfe9
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume exists coord le len 29a8affd8563: P2 M Ground Theory Heights  Heights Finite Covolume exists coord le len 29a8affd8563
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume exists coord le len 29a8affd8563 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume exists coord le len 29a8affd8563 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLatticePointsBelowFinite.lean#L24-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PLatticePointsBelowFinite.lean#L24-L61

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_Imports
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_CoerciveOfPositiveDefinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLatticePointsBelowFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix
open scoped ComplexOrder
noncomputable section
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_coord_le_len_29a8affd8563 {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (g : archUnitary h v) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (y : InfinitePlace E → ι → ℂ) w i,
      ‖y w i‖ ≤ K * M.len (invApply g y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«exists_coord_le_len» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_exists_coord_le_len_29a8affd8563
