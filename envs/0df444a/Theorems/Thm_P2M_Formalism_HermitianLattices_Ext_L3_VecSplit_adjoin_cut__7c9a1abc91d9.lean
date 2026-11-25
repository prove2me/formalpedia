-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_adjoin_cut__7c9a1abc91d9
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_adjoin_cut__7c9a1abc91d9
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:57:47.466128+00:00
-- url     : https://prove2.me/theorems/4716a443-24c8-493b-a863-e2a6af89d12d
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Vec Split adjoin cut  7c9a1abc91d9: P2 M Formalism Hermitian Lattices Ext L3 Vec Split adjoin cut  7c9a1abc91d9
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Vec Split adjoin cut  7c9a1abc91d9 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Vec Split adjoin cut  7c9a1abc91d9 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L88-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L88-L108

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjOMemHcompl
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open Formalism.HermitianLattices.Ext.L3.VecSplit
variable (S : VecSplit h h')

theorem P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_adjoin_cut__7c9a1abc91d9 (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L) : S.adjoin (S.cut L) = L := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«VecSplit».«adjoin_cut'» := P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_adjoin_cut__7c9a1abc91d9
