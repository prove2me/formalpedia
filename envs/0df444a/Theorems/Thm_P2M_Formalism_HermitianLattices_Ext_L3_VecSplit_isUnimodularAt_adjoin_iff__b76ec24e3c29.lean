-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isUnimodularAt_adjoin_iff__b76ec24e3c29
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isUnimodularAt_adjoin_iff__b76ec24e3c29
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:56:46.050294+00:00
-- url     : https://prove2.me/theorems/d4458f10-8e6f-4b3e-807c-4d801ed2df7e
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Vec Split is Unimodular At adjoin iff  b76ec24e3c29: P2 M Formalism Hermitian Lattices Ext L3 Vec Split is Unimodular At adjoin iff  b76ec24e3c29
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Vec Split is Unimodular At adjoin iff  b76ec24e3c29 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Vec Split is Unimodular At adjoin iff  b76ec24e3c29 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L353-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsUnimodularAtAdjoinIff.lean#L353-L367

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

theorem P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isUnimodularAt_adjoin_iff__b76ec24e3c29 (hs : h.IsSymm) (h1 : h S.x₀ S.x₀ = 1)
    (L' : Submodule (𝓞 K) V') (p : Ideal (𝓞 K)) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h p (S.adjoin L') ↔ Formalism.HermitianLatticesTheory.IsUnimodularAt h' p L' := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«VecSplit».«isUnimodularAt_adjoin_iff'» := P2M_Formalism_HermitianLattices_Ext_L3_VecSplit_isUnimodularAt_adjoin_iff__b76ec24e3c29
