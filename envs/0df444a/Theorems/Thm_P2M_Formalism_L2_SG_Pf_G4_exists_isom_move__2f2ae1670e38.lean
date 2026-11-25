-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_G4_exists_isom_move__2f2ae1670e38
-- name    : P2M_Formalism_L2_SG_Pf_G4_exists_isom_move__2f2ae1670e38
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:57:49.198448+00:00
-- url     : https://prove2.me/theorems/5a35061f-de0b-4046-b832-62799732c2d7
-- title:
--   P2 M Formalism L2 SG Pf G4 exists isom move  2f2ae1670e38: P2 M Formalism L2 SG Pf G4 exists isom move  2f2ae1670e38
-- statement:
--   The P2 M Formalism L2 SG Pf G4 exists isom move  2f2ae1670e38 construction uses the P2 M Formalism L2 SG Pf G4 exists isom move  2f2ae1670e38 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsIsomScale.lean#L14-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsIsomScale.lean#L14-L84

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

theorem P2M_Formalism_L2_SG_Pf_G4_exists_isom_move__2f2ae1670e38 (hs : h.IsSymm) {x y : V} (hxy : h x x = h y y)
    (hb : h x x - h y x ≠ 0) :
    ∃ τ ∈ Formalism.HermitianLatticesTheory.isom h, τ x = y ∧ (∀ v, h x v = 0 → h y v = 0 → τ v = v) ∧
      ∀ W : Submodule K V, x ∈ W → y ∈ W → ∀ v, v ∈ W ↔ τ v ∈ W := by sorry

alias «Formalism».«L2».«SG».«Pf».«G4».«exists_isom_move'» := P2M_Formalism_L2_SG_Pf_G4_exists_isom_move__2f2ae1670e38
