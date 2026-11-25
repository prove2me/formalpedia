-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_LIOrb_OrbF_conj_mem_autSub__b1b53b92a341
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_LIOrb_OrbF_conj_mem_autSub__b1b53b92a341
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T07:57:55.901127+00:00
-- url     : https://prove2.me/theorems/ffb240f9-68a1-4748-bcc5-289a949aa71e
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 LIOrb Orb F conj mem aut Sub  b1b53b92a341: P2 M Formalism Hermitian Lattices Ext L3 LIOrb Orb F conj mem aut Sub  b1b53b92a341
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 LIOrb Orb F conj mem aut Sub  b1b53b92a341 construction uses the P2 M Formalism Hermitian Lattices Ext L3 LIOrb Orb F conj mem aut Sub  b1b53b92a341 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjMemAutSub.lean#L108-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjMemAutSub.lean#L108-L111

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExtHomInjective
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsGlobalOfFibLocNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomMapOfEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjMemAutSub
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

theorem P2M_Formalism_HermitianLattices_Ext_L3_LIOrb_OrbF_conj_mem_autSub__b1b53b92a341 {g u : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {A : Submodule (𝓞 K) V}
    (hu : u ∈ autSub h (Formalism.HermitianLatticesTheory.gmap g A)) : g⁻¹ * u * g ∈ autSub h A := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«LIOrb».«OrbF».«conj_mem_autSub'» := P2M_Formalism_HermitianLattices_Ext_L3_LIOrb_OrbF_conj_mem_autSub__b1b53b92a341
