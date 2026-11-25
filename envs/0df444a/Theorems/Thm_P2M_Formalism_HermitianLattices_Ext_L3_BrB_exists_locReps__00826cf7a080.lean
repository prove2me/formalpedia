-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_BrB_exists_locReps__00826cf7a080
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_BrB_exists_locReps__00826cf7a080
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:55.85987+00:00
-- url     : https://prove2.me/theorems/42054ac4-bb49-4ca1-b7b9-42745c1af958
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Br B exists loc Reps  00826cf7a080: P2 M Formalism Hermitian Lattices Ext L3 Br B exists loc Reps  00826cf7a080
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Br B exists loc Reps  00826cf7a080 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Br B exists loc Reps  00826cf7a080 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsLocReps.lean#L118-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsLocReps.lean#L118-L141

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralLatOfForall
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_FinIntermediate
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocReps
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

theorem P2M_Formalism_HermitianLattices_Ext_L3_BrB_exists_locReps__00826cf7a080 (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : ∃ s, IsLocReps S L 𝔭 s := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«BrB».«exists_locReps'» := P2M_Formalism_HermitianLattices_Ext_L3_BrB_exists_locReps__00826cf7a080
