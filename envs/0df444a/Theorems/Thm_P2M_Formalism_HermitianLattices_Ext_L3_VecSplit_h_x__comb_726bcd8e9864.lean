-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_h_x__comb_726bcd8e9864
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_h_x__comb_726bcd8e9864
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:38:47.298592+00:00
-- url     : https://prove2.me/theorems/fb08f219-a42b-42b0-9f83-58d0aeea2b6e
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Vec Split h x  comb 726bcd8e9864: P2 M Formalism Hermitian Lattices Ext L3 Vec Split h x  comb 726bcd8e9864
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Vec Split h x  comb 726bcd8e9864 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Vec Split h x  comb 726bcd8e9864 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L34-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L34-L35

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

theorem P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_h_x__comb_726bcd8e9864 (c : K) (a : V') : h S.x₀ (c • S.x₀ + S.ι a) = c * h S.x₀ S.x₀ := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«VecSplit».«h_x₀_comb» := P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_h_x__comb_726bcd8e9864
