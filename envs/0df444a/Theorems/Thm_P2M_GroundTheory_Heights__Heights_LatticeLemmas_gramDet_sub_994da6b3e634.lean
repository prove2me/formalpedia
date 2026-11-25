-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_sub_994da6b3e634
-- name    : P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_sub_994da6b3e634
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T09:35:16.029496+00:00
-- url     : https://prove2.me/theorems/d1d74acc-3471-595d-b4e8-b1478fbefee6
-- title:
--   P2 M Ground Theory Heights  Heights Lattice Lemmas gram Det sub 994da6b3e634: P2 M Ground Theory Heights  Heights Lattice Lemmas gram Det sub 994da6b3e634
-- statement:
--   The P2 M Ground Theory Heights  Heights Lattice Lemmas gram Det sub 994da6b3e634 construction uses the P2 M Ground Theory Heights  Heights Lattice Lemmas gram Det sub 994da6b3e634 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSublattice.lean#L11-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/LatticeLemmas/PSublattice.lean#L11-L20

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PSublattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LatticeLemmas
open NumberField GroundTheory.Heights₂.Heights
noncomputable section

theorem P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_sub_994da6b3e634 {K : Type*} [Field K] [NumberField K] (M : HermitianBundle K)
    (F : Submodule (𝓞 K) M.carrier) (σ : K →+* ℂ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → F) :
    gramDet (M.sub F).metric σ s = gramDet M.metric σ (fun i ↦ (s i : M.carrier)) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«LatticeLemmas».«gramDet_sub» := P2M_GroundTheory_Heights__Heights_LatticeLemmas_gramDet_sub_994da6b3e634
