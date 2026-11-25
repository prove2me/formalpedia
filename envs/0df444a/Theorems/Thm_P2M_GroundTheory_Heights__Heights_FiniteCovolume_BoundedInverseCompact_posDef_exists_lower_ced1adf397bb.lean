-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_posDef_exists_lower_ced1adf397bb
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_posDef_exists_lower_ced1adf397bb
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:41:43.458449+00:00
-- url     : https://prove2.me/theorems/6d4e9a68-7351-4faf-884c-df06909cd59d
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Bounded Inverse Compact pos Def exists lower ced1adf397bb: P2 M Ground Theory Heights  Heights Finite Covolume Bounded Inverse Compact pos Def exist
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Bounded Inverse Compact pos Def exists lower ced1adf397bb construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Bounded Inverse Compact pos Def exists lower ced1adf397bb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PBoundedInverseCompact.lean#L18-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PBoundedInverseCompact.lean#L18-L52

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_SecondCountableTopologyArchUnitary
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StBoundedInverseCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PBoundedInverseCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
open scoped ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.FiniteCovolume.BoundedInverseCompact
variable {ι : Type*} [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_posDef_exists_lower_ced1adf397bb {P : Matrix ι ι ℂ} (hP : P.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ y : ι → ℂ, c * ‖y‖ ^ 2 ≤ (star y ⬝ᵥ (P *ᵥ y)).re := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«BoundedInverseCompact».«posDef_exists_lower» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_posDef_exists_lower_ced1adf397bb
