-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf_x__7113d86d152c
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf_x__7113d86d152c
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:49:58.147333+00:00
-- url     : https://prove2.me/theorems/3954c61f-14c7-4a35-95cc-9f6f88f0420c
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Split BAux ext Of x  7113d86d152c: P2 M Formalism Hermitian Lattices Ext L3 Split BAux ext Of x  7113d86d152c
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Split BAux ext Of x  7113d86d152c construction uses the P2 M Formalism Hermitian Lattices Ext L3 Split BAux ext Of x  7113d86d152c property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtOfSymmApply.lean#L168-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtOfSymmApply.lean#L168-L170

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

theorem P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf_x__7113d86d152c (S : VecSplit h h') (g' : V' ≃ₗ[K] V') : extOf S g' S.x₀ = S.x₀ := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«SplitBAux».«extOf_x₀» := P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf_x__7113d86d152c
