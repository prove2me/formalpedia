-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf___ee27e8a53762
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf___ee27e8a53762
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:33:11.404005+00:00
-- url     : https://prove2.me/theorems/9e72f0b0-1831-4ec0-9ab7-14da2da7da28
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Split BAux ext Of   ee27e8a53762: P2 M Formalism Hermitian Lattices Ext L3 Split BAux ext Of   ee27e8a53762
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Split BAux ext Of   ee27e8a53762 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Split BAux ext Of   ee27e8a53762 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtOfSymmApply.lean#L172-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExtOfSymmApply.lean#L172-L175

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

theorem P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf___ee27e8a53762 (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (a : V') :
    extOf S g' (S.ι a) = S.ι (g' a) := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«SplitBAux».«extOf_ι» := P2M_Formalism_HermitianLattices_Ext_L3_SplitBAux_extOf___ee27e8a53762
