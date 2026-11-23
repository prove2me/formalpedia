-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_G4_exists_primitive__0bf0807a5daa
-- name    : P2M_Formalism_L2_SG_Pf_G4_exists_primitive__0bf0807a5daa
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:41.42407+00:00
-- url     : https://prove2.me/theorems/ada9ac3f-a3af-4aef-ab79-ec49921ab527
-- title:
--   P2 M Formalism L2 SG Pf G4 exists primitive  0bf0807a5daa: P2 M Formalism L2 SG Pf G4 exists primitive  0bf0807a5daa
-- statement:
--   The P2 M Formalism L2 SG Pf G4 exists primitive  0bf0807a5daa construction uses the P2 M Formalism L2 SG Pf G4 exists primitive  0bf0807a5daa property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/AdelicThetaPoissonSummation.lean#L17-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/AdelicThetaPoissonSummation.lean#L17-L53

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsOrthTransfer
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AdelicThetaPoissonSummation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Module
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.G4
open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K} {W : Submodule K V} {M : AddSubgroup V}

theorem P2M_Formalism_L2_SG_Pf_G4_exists_primitive__0bf0807a5daa (hS : IsHermSemilocal S) (hM : IsLatIn S h W M) {ξ w : V} (hξ : ξ ∈ W)
    (hw : w ∈ W) (hn : h w ξ ≠ 0) :
    ∃ l : K, l ≠ 0 ∧ l • ξ ∈ M ∧ ∀ c : K, c • ξ ∈ M → c * l⁻¹ ∈ S := by sorry

alias «Formalism».«L2».«SG».«Pf».«G4».«exists_primitive'» := P2M_Formalism_L2_SG_Pf_G4_exists_primitive__0bf0807a5daa
