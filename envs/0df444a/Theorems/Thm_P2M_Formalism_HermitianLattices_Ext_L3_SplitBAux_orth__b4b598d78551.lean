-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_orth__b4b598d78551
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_orth__b4b598d78551
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:56:58.967681+00:00
-- url     : https://prove2.me/theorems/f3690da1-47d1-4c92-b8d5-9dc2dbaf78ce
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Split BAux orth  b4b598d78551: P2 M Formalism Hermitian Lattices Ext L3 Split BAux orth  b4b598d78551
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Split BAux orth  b4b598d78551 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Split BAux orth  b4b598d78551 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtOfSymmApply.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtOfSymmApply.lean#L27-L28

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsUnimodularAtAdjoinIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtOfSymmApply
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_orth__ee462835f427

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

theorem P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_orth__b4b598d78551 (hs : h.IsSymm) (S : VecSplit h h') (a : V') : h (S.ι a) S.x₀ = 0 := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«SplitBAux».«orth'» := P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_orth__b4b598d78551
