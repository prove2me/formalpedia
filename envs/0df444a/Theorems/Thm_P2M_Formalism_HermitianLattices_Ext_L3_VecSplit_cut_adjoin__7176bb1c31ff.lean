-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_cut_adjoin__7176bb1c31ff
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_cut_adjoin__7176bb1c31ff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:58:16.520964+00:00
-- url     : https://prove2.me/theorems/4e8df26b-3acd-4ffa-8518-b6cab2874d4e
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Vec Split cut adjoin  7176bb1c31ff: P2 M Formalism Hermitian Lattices Ext L3 Vec Split cut adjoin  7176bb1c31ff
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Vec Split cut adjoin  7176bb1c31ff construction uses the P2 M Formalism Hermitian Lattices Ext L3 Vec Split cut adjoin  7176bb1c31ff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L75-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L75-L86

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

theorem P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_cut_adjoin__7176bb1c31ff (L' : Submodule (𝓞 K) V') : S.cut (S.adjoin L') = L' := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«VecSplit».«cut_adjoin'» := P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_cut_adjoin__7176bb1c31ff
