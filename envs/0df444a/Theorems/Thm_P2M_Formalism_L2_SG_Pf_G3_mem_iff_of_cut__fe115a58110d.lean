-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_G3_mem_iff_of_cut__fe115a58110d
-- name    : P2M_Formalism_L2_SG_Pf_G3_mem_iff_of_cut__fe115a58110d
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:31:45.4198+00:00
-- url     : https://prove2.me/theorems/a3e13523-f480-5f47-b767-515358ef0a51
-- title:
--   P2 M Formalism L2 SG Pf G3 mem iff of cut  fe115a58110d: P2 M Formalism L2 SG Pf G3 mem iff of cut  fe115a58110d
-- statement:
--   The P2 M Formalism L2 SG Pf G3 mem iff of cut  fe115a58110d construction uses the P2 M Formalism L2 SG Pf G3 mem iff of cut  fe115a58110d property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/MemSpanIffSpanS.lean#L83-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/MemSpanIffSpanS.lean#L83-L118

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_SplitAtOf
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_MemSpanIffSpanS
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
noncomputable section
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G3
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem P2M_Formalism_L2_SG_Pf_G3_mem_iff_of_cut__fe115a58110d {M N : AddSubgroup V} (hMs : ∀ a ∈ S, ∀ m ∈ M, a • m ∈ M)
    (hNs : ∀ a ∈ S, ∀ m ∈ N, a • m ∈ N) {x X : V} (hx : x ∈ M) (hX : X ∈ N)
    (hMx : ∀ m ∈ M, h x m * (h x x)⁻¹ ∈ S) (hNX : ∀ m ∈ N, h X m * (h X X)⁻¹ ∈ S)
    {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hgx : g x = X) (hxx : h x x ≠ 0)
    (hcut : ∀ v, v ∈ cutM h M x ↔ g v ∈ cutM h N X) : ∀ v, v ∈ M ↔ g v ∈ N := by sorry

alias «Formalism».«L2».«SG».«Pf».«G3».«mem_iff_of_cut'» := P2M_Formalism_L2_SG_Pf_G3_mem_iff_of_cut__fe115a58110d
