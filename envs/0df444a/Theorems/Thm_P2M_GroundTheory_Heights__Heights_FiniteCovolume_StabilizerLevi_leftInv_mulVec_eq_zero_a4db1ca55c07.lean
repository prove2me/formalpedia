-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leftInv_mulVec_eq_zero_a4db1ca55c07
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leftInv_mulVec_eq_zero_a4db1ca55c07
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:19:57.098217+00:00
-- url     : https://prove2.me/theorems/685f9621-3b80-452d-927f-e0665bd5c928
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi left Inv mul Vec eq zero a4db1ca55c07: P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi left Inv mul Vec eq zero
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi left Inv mul Vec eq zero a4db1ca55c07 construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Stabilizer Levi left Inv mul Vec eq zero a4db1ca55c07 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L66-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLeviMatrices.lean#L66-L67

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviMatrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Heights₂.Heights.FiniteCovolume.StabilizerLevi
open Matrix
noncomputable section
set_option linter.unusedSectionVars false
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {H : Matrix ι ι ℂ} {B : Matrix ι κ ℂ}

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leftInv_mulVec_eq_zero_a4db1ca55c07 {X : ι → ℂ} (hBX : Bᴴ *ᵥ (H *ᵥ X) = 0) : leftInv H B *ᵥ X = 0 := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«StabilizerLevi».«leftInv_mulVec_eq_zero» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leftInv_mulVec_eq_zero_a4db1ca55c07
