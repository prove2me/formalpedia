-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_x__not_mem_range_04f72e8df2db
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_x__not_mem_range_04f72e8df2db
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:05:22.277615+00:00
-- url     : https://prove2.me/theorems/1bbc62d4-674b-41b6-a15a-d0d59cd7cfce
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Vec Split x  not mem range 04f72e8df2db: P2 M Formalism Hermitian Lattices Ext L3 Vec Split x  not mem range 04f72e8df2db
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Vec Split x  not mem range 04f72e8df2db construction uses the P2 M Formalism Hermitian Lattices Ext L3 Vec Split x  not mem range 04f72e8df2db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L50-L54

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

theorem P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_x__not_mem_range_04f72e8df2db (a : V') : S.ι a ≠ S.x₀ := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«VecSplit».«x₀_not_mem_range» := P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_x__not_mem_range_04f72e8df2db
