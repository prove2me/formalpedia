-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_x__mem_adjoin_e436df04d130
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_x__mem_adjoin_e436df04d130
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:46:25.377086+00:00
-- url     : https://prove2.me/theorems/cc4e3ff1-4dbc-4722-a821-a850d55d7f52
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Vec Split x  mem adjoin e436df04d130: P2 M Formalism Hermitian Lattices Ext L3 Vec Split x  mem adjoin e436df04d130
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Vec Split x  mem adjoin e436df04d130 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Vec Split x  mem adjoin e436df04d130 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L385-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L385-L386

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

theorem P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_x__mem_adjoin_e436df04d130 (S : VecSplit h h') (L' : Submodule (𝓞 K) V') :
    S.x₀ ∈ S.adjoin L' := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«VecSplit».«x₀_mem_adjoin» := P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_x__mem_adjoin_e436df04d130
