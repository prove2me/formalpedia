-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_orth__ee462835f427
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_orth__ee462835f427
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:37:27.391252+00:00
-- url     : https://prove2.me/theorems/c90a1ab5-0df2-4890-a8c5-789731084807
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Vec Split orth  ee462835f427: P2 M Formalism Hermitian Lattices Ext L3 Vec Split orth  ee462835f427
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Vec Split orth  ee462835f427 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Vec Split orth  ee462835f427 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L116-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L116-L117

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

theorem P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_orth__ee462835f427 (hs : h.IsSymm) (a : V') : h (S.ι a) S.x₀ = 0 := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«VecSplit».«orth'» := P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_orth__ee462835f427
