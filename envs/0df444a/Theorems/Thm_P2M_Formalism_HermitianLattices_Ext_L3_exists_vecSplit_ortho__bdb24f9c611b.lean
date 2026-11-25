-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_exists_vecSplit_ortho__bdb24f9c611b
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_exists_vecSplit_ortho__bdb24f9c611b
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:57:44.647904+00:00
-- url     : https://prove2.me/theorems/fb1633e2-6790-4fe7-9b56-de7696120a76
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 exists vec Split ortho  bdb24f9c611b: P2 M Formalism Hermitian Lattices Ext L3 exists vec Split ortho  bdb24f9c611b
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 exists vec Split ortho  bdb24f9c611b construction uses the P2 M Formalism Hermitian Lattices Ext L3 exists vec Split ortho  bdb24f9c611b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L239-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L239-L291

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

theorem P2M_Formalism_HermitianLattices_Ext_L3_exists_vecSplit_ortho__bdb24f9c611b {I : Submodule (𝓞 K) V} {I' : Submodule (𝓞 K) V'} {n : ℕ}
    (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I (n + 1)) (hI' : Formalism.HermitianLatticesTheory.IsOrthoLattice h' I' n) :
    ∃ S : VecSplit h h', h S.x₀ S.x₀ = 1 ∧ S.adjoin I' = I := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«exists_vecSplit_ortho'» := P2M_Formalism_HermitianLattices_Ext_L3_exists_vecSplit_ortho__bdb24f9c611b
