-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isIntegralLat_adjoin_iff__c3220d48d8b8
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isIntegralLat_adjoin_iff__c3220d48d8b8
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:57:31.769962+00:00
-- url     : https://prove2.me/theorems/2ec07ab8-4795-4423-b506-ba7facac84e0
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Vec Split is Integral Lat adjoin iff  c3220d48d8b8: P2 M Formalism Hermitian Lattices Ext L3 Vec Split is Integral Lat adjoin iff  c3220d48d8b8
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Vec Split is Integral Lat adjoin iff  c3220d48d8b8 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Vec Split is Integral Lat adjoin iff  c3220d48d8b8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L180-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L180-L195

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

theorem P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isIntegralLat_adjoin_iff__c3220d48d8b8 (hs : h.IsSymm) (h1 : h S.x₀ S.x₀ = 1) (L' : Submodule (𝓞 K) V') :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (S.adjoin L') ↔ Formalism.HermitianLatticesTheory.IsIntegralLat h' L' := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«VecSplit».«isIntegralLat_adjoin_iff'» := P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isIntegralLat_adjoin_iff__c3220d48d8b8
