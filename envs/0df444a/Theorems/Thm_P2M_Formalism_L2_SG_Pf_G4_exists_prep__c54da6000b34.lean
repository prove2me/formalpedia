-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_G4_exists_prep__c54da6000b34
-- name    : P2M_Formalism_L2_SG_Pf_G4_exists_prep__c54da6000b34
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:45.291807+00:00
-- url     : https://prove2.me/theorems/64817980-2cb3-45ff-a4ef-c5b120fba0b1
-- title:
--   P2 M Formalism L2 SG Pf G4 exists prep  c54da6000b34: P2 M Formalism L2 SG Pf G4 exists prep  c54da6000b34
-- statement:
--   The P2 M Formalism L2 SG Pf G4 exists prep  c54da6000b34 construction uses the P2 M Formalism L2 SG Pf G4 exists prep  c54da6000b34 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsIsomScale.lean#L140-L162
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsIsomScale.lean#L140-L162

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

theorem P2M_Formalism_L2_SG_Pf_G4_exists_prep__c54da6000b34 (hs : h.IsSymm) (h2 : (2 : K) ≠ 0) {W₁ W₂ : Submodule K V}
    {φ : V ≃ₗ[K] V} (hφ : φ ∈ Formalism.HermitianLatticesTheory.isom h) (hW : ∀ v, v ∈ W₁ ↔ φ v ∈ W₂) {x X : V}
    (hx : x ∈ W₁) (hX : X ∈ W₂) (hxX : h x x = h X X) (hx0 : h x x ≠ 0) :
    ∃ φ' ∈ Formalism.HermitianLatticesTheory.isom h, φ' x = X ∧ (∀ v, v ∈ cutW h W₁ x ↔ φ' v ∈ cutW h W₂ X) ∧
      ∀ v, (∀ w ∈ W₁, h w v = 0) → φ' v = φ v := by sorry

alias «Formalism».«L2».«SG».«Pf».«G4».«exists_prep'» := P2M_Formalism_L2_SG_Pf_G4_exists_prep__c54da6000b34
