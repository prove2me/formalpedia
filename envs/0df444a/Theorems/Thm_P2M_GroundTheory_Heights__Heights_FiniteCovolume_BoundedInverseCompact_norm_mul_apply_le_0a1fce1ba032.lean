-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_norm_mul_apply_le_0a1fce1ba032
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_norm_mul_apply_le_0a1fce1ba032
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:39:43.19696+00:00
-- url     : https://prove2.me/theorems/cadc216d-ae09-4b37-84ea-bbb6564f2cf0
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Bounded Inverse Compact norm mul apply le 0a1fce1ba032: P2 M Ground Theory Heights  Heights Finite Covolume Bounded Inverse Compact norm mul apply l
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Bounded Inverse Compact norm mul apply le 0a1fce1ba032 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Bounded Inverse Compact norm mul apply le 0a1fce1ba032 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PBoundedInverseCompact.lean#L56-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PBoundedInverseCompact.lean#L56-L60

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
omit [Fintype ι]

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_norm_mul_apply_le_0a1fce1ba032 {m κ : Type*} [Fintype κ] (A : Matrix m κ ℂ) (B : Matrix κ ι ℂ)
    (i : m) (j : ι) : ‖(A * B) i j‖ ≤ ∑ k, ‖A i k‖ * ‖B k j‖ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«BoundedInverseCompact».«norm_mul_apply_le» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_BoundedInverseCompact_norm_mul_apply_le_0a1fce1ba032
