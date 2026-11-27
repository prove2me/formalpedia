-- Prove2me | Theorems.Thm_P2M_GroundTheory_Automorphic_CompactRep_kProj___b6ac11bd4d0a
-- name    : P2M_GroundTheory_Automorphic_CompactRep_kProj___b6ac11bd4d0a
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T13:13:18.734382+00:00
-- url     : https://prove2.me/theorems/799677f7-b931-5b9c-90a2-c613536d1741
-- title:
--   P2 M Ground Theory Automorphic Compact Rep k Proj   b6ac11bd4d0a: P2 M Ground Theory Automorphic Compact Rep k Proj   b6ac11bd4d0a
-- statement:
--   The P2 M Ground Theory Automorphic Compact Rep k Proj   b6ac11bd4d0a construction uses the P2 M Ground Theory Automorphic Compact Rep k Proj   b6ac11bd4d0a property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KProjApplyEqSelfIff.lean#L41-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/KProjApplyEqSelfIff.lean#L41-L46

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KFinite
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_GenWindow
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_KProjApplyEqSelfIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.CompactRep
open Module Set RestrictedTensor
variable {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
  [T2Space K] {X : Type*} [AddCommGroup X] [Module ℂ X] {σ : Representation ℂ K X}
variable (hσ : IsKFinite σ) {c : Submodule (MonoidAlgebra ℂ K) σ.asModule}
  (hc : c ∈ isotypicComponents (MonoidAlgebra ℂ K) σ.asModule)

theorem P2M_GroundTheory_Automorphic_CompactRep_kProj___b6ac11bd4d0a (k : K) (v : X) : kProj hσ hc (σ k v) = σ k (kProj hσ hc v) := by sorry

alias «GroundTheory».«Automorphic».«CompactRep».«kProj_σ» := P2M_GroundTheory_Automorphic_CompactRep_kProj___b6ac11bd4d0a
