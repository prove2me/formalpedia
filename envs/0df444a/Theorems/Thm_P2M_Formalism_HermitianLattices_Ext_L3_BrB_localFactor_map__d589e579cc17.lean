-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_BrB_localFactor_map__d589e579cc17
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_BrB_localFactor_map__d589e579cc17
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:54:04.574465+00:00
-- url     : https://prove2.me/theorems/96435491-c036-55f7-a1bd-73616a742409
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Br B local Factor map  d589e579cc17: P2 M Formalism Hermitian Lattices Ext L3 Br B local Factor map  d589e579cc17
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Br B local Factor map  d589e579cc17 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Br B local Factor map  d589e579cc17 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SumLocRepsEq.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SumLocRepsEq.lean#L71-L74

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralLatOfForall
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumLocRepsEq
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BrB
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem P2M_Formalism_HermitianLattices_Ext_L3_BrB_localFactor_map__d589e579cc17 {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (T : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) : lamP h (Formalism.HermitianLatticesTheory.gmap g T) 𝔭 = lamP h T 𝔭 := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«BrB».«localFactor_map'» := P2M_Formalism_HermitianLattices_Ext_L3_BrB_localFactor_map__d589e579cc17
