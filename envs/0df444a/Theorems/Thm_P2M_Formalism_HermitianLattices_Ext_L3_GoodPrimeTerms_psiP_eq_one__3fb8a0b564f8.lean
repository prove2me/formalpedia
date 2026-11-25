-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_GoodPrimeTerms_psiP_eq_one__3fb8a0b564f8
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_GoodPrimeTerms_psiP_eq_one__3fb8a0b564f8
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:55:40.145425+00:00
-- url     : https://prove2.me/theorems/4bab9bda-8604-4432-be57-41c707c44dac
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Good Prime Terms psi P eq one  3fb8a0b564f8: P2 M Formalism Hermitian Lattices Ext L3 Good Prime Terms psi P eq one  3fb8a0b564f8
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Good Prime Terms psi P eq one  3fb8a0b564f8 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Good Prime Terms psi P eq one  3fb8a0b564f8 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsIntegralAtLocF.lean#L70-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsIntegralAtLocF.lean#L70-L108

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeOfFibLocNeZeroGood
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFibGEqProd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralAtLocF
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.GoodPrimeTerms
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open UnimodularLocalization

theorem P2M_Formalism_HermitianLattices_Ext_L3_GoodPrimeTerms_psiP_eq_one__3fb8a0b564f8 (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    (hvL : vd h L 𝔭 = 0) (hvn : vF 𝔭 n = 0) : psiP S L 𝔭 = 1 := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«GoodPrimeTerms».«psiP_eq_one'» := P2M_Formalism_HermitianLattices_Ext_L3_GoodPrimeTerms_psiP_eq_one__3fb8a0b564f8
