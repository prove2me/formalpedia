-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_h_x__decomp_4047aa1272f4
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_h_x__decomp_4047aa1272f4
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:11:46.706532+00:00
-- url     : https://prove2.me/theorems/12b9cebd-f5cb-56f2-b7d5-4fde16cf145f
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Split BAux h x  decomp 4047aa1272f4: P2 M Formalism Hermitian Lattices Ext L3 Split BAux h x  decomp 4047aa1272f4
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Split BAux h x  decomp 4047aa1272f4 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Split BAux h x  decomp 4047aa1272f4 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtOfSymmApply.lean#L17-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtOfSymmApply.lean#L17-L19

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.SplitBAux
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_h_x__decomp_4047aa1272f4 (S : VecSplit h h') (c : K) (a : V') :
    h S.x₀ (c • S.x₀ + S.ι a) = c * h S.x₀ S.x₀ := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«SplitBAux».«h_x₀_decomp» := P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_h_x__decomp_4047aa1272f4
