-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isOrthoLattice_adjoin__de5b3f982f95
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isOrthoLattice_adjoin__de5b3f982f95
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:57:55.891471+00:00
-- url     : https://prove2.me/theorems/105c87cd-8983-4907-a121-34f430ab8e51
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Vec Split is Ortho Lattice adjoin  de5b3f982f95: P2 M Formalism Hermitian Lattices Ext L3 Vec Split is Ortho Lattice adjoin  de5b3f982f95
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Vec Split is Ortho Lattice adjoin  de5b3f982f95 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Vec Split is Ortho Lattice adjoin  de5b3f982f95 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L197-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L197-L235

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

theorem P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isOrthoLattice_adjoin__de5b3f982f95 (hs : h.IsSymm) (h1 : h S.x₀ S.x₀ = 1)
    {I' : Submodule (𝓞 K) V'} {n : ℕ} (hI' : Formalism.HermitianLatticesTheory.IsOrthoLattice h' I' n) :
    Formalism.HermitianLatticesTheory.IsOrthoLattice h (S.adjoin I') (n + 1) := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«VecSplit».«isOrthoLattice_adjoin'» := P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isOrthoLattice_adjoin__de5b3f982f95
