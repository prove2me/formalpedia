-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_LIOrb_OrbF_stab_actV__5aea468bc21b
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_LIOrb_OrbF_stab_actV__5aea468bc21b
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:52:35.193367+00:00
-- url     : https://prove2.me/theorems/3721c307-30d3-5977-8b3e-6309b9b3372f
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 LIOrb Orb F stab act V  5aea468bc21b: P2 M Formalism Hermitian Lattices Ext L3 LIOrb Orb F stab act V  5aea468bc21b
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 LIOrb Orb F stab act V  5aea468bc21b construction uses the P2 M Formalism Hermitian Lattices Ext L3 LIOrb Orb F stab act V  5aea468bc21b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjMemAutSub.lean#L75-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ConjMemAutSub.lean#L75-L79

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

theorem P2M_Formalism_HermitianLattices_Ext_L3_LIOrb_OrbF_stab_actV__5aea468bc21b (T : Submodule (𝓞 K) V') :
    @MulAction.stabilizer _ _ _ (actV' h') T = (autSub h' T).subgroupOf (Formalism.HermitianLatticesTheory.isom h') := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«LIOrb».«OrbF».«stab_actV'» := P2M_Formalism_HermitianLattices_Ext_L3_LIOrb_OrbF_stab_actV__5aea468bc21b
