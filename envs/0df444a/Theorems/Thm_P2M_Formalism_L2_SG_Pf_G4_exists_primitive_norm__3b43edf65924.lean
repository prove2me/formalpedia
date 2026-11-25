-- Prove2me | Theorems.Thm_P2M_Formalism_L2_SG_Pf_G4_exists_primitive_norm__3b43edf65924
-- name    : P2M_Formalism_L2_SG_Pf_G4_exists_primitive_norm__3b43edf65924
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:57:08.628004+00:00
-- url     : https://prove2.me/theorems/15436482-58c1-4ede-85c9-92bf7ee50b73
-- title:
--   P2 M Formalism L2 SG Pf G4 exists primitive norm  3b43edf65924: P2 M Formalism L2 SG Pf G4 exists primitive norm  3b43edf65924
-- statement:
--   The P2 M Formalism L2 SG Pf G4 exists primitive norm  3b43edf65924 construction uses the P2 M Formalism L2 SG Pf G4 exists primitive norm  3b43edf65924 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/AdelicThetaPoissonSummation.lean#L55-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/DualFamilyCounting/AdelicThetaPoissonSummation.lean#L55-L79

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

theorem P2M_Formalism_L2_SG_Pf_G4_exists_primitive_norm__3b43edf65924 (hS : IsHermSemilocal S) (hM : IsLatIn S h W M) {ξ : V} (hξ : ξ ∈ W)
    {u : K} (hu : IsUnitIn S u) (hξu : h ξ ξ = u) :
    ∃ y ∈ M, y ≠ 0 ∧ (∃ l : K, y = l • ξ) ∧ (∀ c : K, c • y ∈ M → c ∈ S) ∧
      ∃ a ∈ S, h y y = star a * a * u := by sorry

alias «Formalism».«L2».«SG».«Pf».«G4».«exists_primitive_norm'» := P2M_Formalism_L2_SG_Pf_G4_exists_primitive_norm__3b43edf65924
