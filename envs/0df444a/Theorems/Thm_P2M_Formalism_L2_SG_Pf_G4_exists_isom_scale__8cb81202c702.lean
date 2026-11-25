-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_G4_exists_isom_scale__8cb81202c702
-- name    : P2M_Formalism_L2_SG_Pf_G4_exists_isom_scale__8cb81202c702
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:58:09.821314+00:00
-- url     : https://prove2.me/theorems/1c669b87-ff25-4009-a982-f2ff96d25662
-- title:
--   P2 M Formalism L2 SG Pf G4 exists isom scale  8cb81202c702: P2 M Formalism L2 SG Pf G4 exists isom scale  8cb81202c702
-- statement:
--   The P2 M Formalism L2 SG Pf G4 exists isom scale  8cb81202c702 construction uses the P2 M Formalism L2 SG Pf G4 exists isom scale  8cb81202c702 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsIsomScale.lean#L86-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsIsomScale.lean#L86-L107

import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_AdelicThetaPoissonSummation
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_DualFamilyCounting_ExistsIsomScale
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
variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem P2M_Formalism_L2_SG_Pf_G4_exists_isom_scale__8cb81202c702 (hs : h.IsSymm) {z : V} (hz : h z z ≠ 0) {b : K} (hb : star b * b = 1) :
    ∃ ψ ∈ Formalism.HermitianLatticesTheory.isom h, ψ z = b • z ∧ (∀ v, h z v = 0 → ψ v = v) ∧
      ∀ W : Submodule K V, z ∈ W → ∀ v, v ∈ W ↔ ψ v ∈ W := by sorry

alias «Formalism».«L2».«SG».«Pf».«G4».«exists_isom_scale'» := P2M_Formalism_L2_SG_Pf_G4_exists_isom_scale__8cb81202c702
