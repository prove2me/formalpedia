-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_G4_sd_main__321961475f15
-- name    : P2M_Formalism_L2_SG_Pf_G4_sd_main__321961475f15
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:32.509886+00:00
-- url     : https://prove2.me/theorems/4e6a87fd-7f0c-43bd-8f01-7bde00ff4f46
-- title:
--   P2 M Formalism L2 SG Pf G4 sd main  321961475f15: P2 M Formalism L2 SG Pf G4 sd main  321961475f15
-- statement:
--   The P2 M Formalism L2 SG Pf G4 sd main  321961475f15 construction uses the P2 M Formalism L2 SG Pf G4 sd main  321961475f15 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsIsomScale.lean#L164-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/ExistsIsomScale.lean#L164-L259

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

theorem P2M_Formalism_L2_SG_Pf_G4_sd_main__321961475f15 [FiniteDimensional K V] (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    (hs : h.IsSymm) (h2 : (2 : K) ≠ 0) (n : ℕ) :
    ∀ (W₁ W₂ : Submodule K V) (M N : AddSubgroup V) (φ : V ≃ₗ[K] V), finrank K W₁ ≤ n →
      NondegOn h W₁ → IsSD S h W₁ M → IsSD S h W₂ N → φ ∈ Formalism.HermitianLatticesTheory.isom h →
      (∀ v, v ∈ W₁ ↔ φ v ∈ W₂) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, (∀ v, (∀ w ∈ W₁, h w v = 0) → g v = φ v) ∧ ∀ v, v ∈ M ↔ g v ∈ N := by sorry

alias «Formalism».«L2».«SG».«Pf».«G4».«sd_main'» := P2M_Formalism_L2_SG_Pf_G4_sd_main__321961475f15
