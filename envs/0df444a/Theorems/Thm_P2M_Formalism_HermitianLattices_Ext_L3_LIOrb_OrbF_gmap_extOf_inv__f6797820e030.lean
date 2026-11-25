-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_LIOrb_OrbF_gmap_extOf_inv__f6797820e030
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_LIOrb_OrbF_gmap_extOf_inv__f6797820e030
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T08:18:31.378217+00:00
-- url     : https://prove2.me/theorems/3b7e5767-1186-417e-b15a-59b38bb34968
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 LIOrb Orb F gmap ext Of inv  f6797820e030: P2 M Formalism Hermitian Lattices Ext L3 LIOrb Orb F gmap ext Of inv  f6797820e030
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 LIOrb Orb F gmap ext Of inv  f6797820e030 construction uses the P2 M Formalism Hermitian Lattices Ext L3 LIOrb Orb F gmap ext Of inv  f6797820e030 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AutSubApplyMem.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AutSubApplyMem.lean#L27-L29

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjMemAutSub
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AutSubApplyMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem P2M_Formalism_HermitianLattices_Ext_L3_LIOrb_OrbF_gmap_extOf_inv__f6797820e030 (S : VecSplit h h') (a : V' ≃ₗ[K] V') (M : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S a⁻¹) (Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S a) M) = M := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«LIOrb».«OrbF».«gmap_extOf_inv'» := P2M_Formalism_HermitianLattices_Ext_L3_LIOrb_OrbF_gmap_extOf_inv__f6797820e030
