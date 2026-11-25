-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_G4_IsSD_exists_unit_norm__db471541043b
-- name    : P2M_Formalism_L2_SG_Pf_G4_IsSD_exists_unit_norm__db471541043b
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:58:37.350976+00:00
-- url     : https://prove2.me/theorems/2ae06515-95c9-48c3-9014-2bf8d167e3f3
-- title:
--   P2 M Formalism L2 SG Pf G4 Is SD exists unit norm  db471541043b: P2 M Formalism L2 SG Pf G4 Is SD exists unit norm  db471541043b
-- statement:
--   The P2 M Formalism L2 SG Pf G4 Is SD exists unit norm  db471541043b construction uses the P2 M Formalism L2 SG Pf G4 Is SD exists unit norm  db471541043b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/AdelicThetaPoissonSummation.lean#L95-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/AdelicThetaPoissonSummation.lean#L95-L105

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

theorem P2M_Formalism_L2_SG_Pf_G4_IsSD_exists_unit_norm__db471541043b (hS : IsHermSemilocal S) (hπ : IsUnif S π) (hs : h.IsSymm)
    (hnd : NondegOn h W) (hM : IsSD S h W M) {ξ : V} (hξ : ξ ∈ W) (hξ0 : ξ ≠ 0) :
    ∃ x ∈ M, IsUnitIn S (h x x) := by sorry

alias «Formalism».«L2».«SG».«Pf».«G4».«IsSD».«exists_unit_norm'» := P2M_Formalism_L2_SG_Pf_G4_IsSD_exists_unit_norm__db471541043b
