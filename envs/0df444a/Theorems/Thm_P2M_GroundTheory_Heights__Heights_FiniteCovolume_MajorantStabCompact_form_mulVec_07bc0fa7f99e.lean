-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantStabCompact_form_mulVec_07bc0fa7f99e
-- name    : P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantStabCompact_form_mulVec_07bc0fa7f99e
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:28:16.737952+00:00
-- url     : https://prove2.me/theorems/ef8fbe9c-315b-557e-a31b-ebf28d558c29
-- title:
--   P2 M Ground Theory Heights  Heights Finite Covolume Majorant Stab Compact form mul Vec 07bc0fa7f99e: P2 M Ground Theory Heights  Heights Finite Covolume Majorant Stab Compact form mul Vec 07bc0fa7f99e
-- statement:
--   The P2 M Ground Theory Heights  Heights Finite Covolume Majorant Stab Compact form mul Vec 07bc0fa7f99e construction uses the P2 M Ground Theory Heights  Heights Finite Covolume Majorant Stab Compact form mul Vec 07bc0fa7f99e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantStabCompact.lean#L14-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PMajorantStabCompact.lean#L14-L21

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_StatementsMajorantStabCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PBoundedInverseCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PMajorantStabCompact
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
open GroundTheory.Heights₂.Heights.FiniteCovolume.MajorantStabCompact

theorem P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantStabCompact_form_mulVec_07bc0fa7f99e {ι : Type*} [Fintype ι] {P A : Matrix ι ι ℂ}
    (hA : (A.map (starRingEnd ℂ))ᵀ * P * A = P) (y : ι → ℂ) :
    star (A *ᵥ y) ⬝ᵥ (P *ᵥ (A *ᵥ y)) = star y ⬝ᵥ (P *ᵥ y) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«FiniteCovolume».«MajorantStabCompact».«form_mulVec» := P2M_GroundTheory_Heights__Heights_FiniteCovolume_MajorantStabCompact_form_mulVec_07bc0fa7f99e
