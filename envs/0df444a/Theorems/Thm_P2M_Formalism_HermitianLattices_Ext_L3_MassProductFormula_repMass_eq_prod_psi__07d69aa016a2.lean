-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_MassProductFormula_repMass_eq_prod_psi__07d69aa016a2
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_MassProductFormula_repMass_eq_prod_psi__07d69aa016a2
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T08:07:34.120903+00:00
-- url     : https://prove2.me/theorems/7b2cc57b-74b0-48f9-a99a-d9fc5c6fc078
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Mass Product Formula rep Mass eq prod psi  07d69aa016a2: P2 M Formalism Hermitian Lattices Ext L3 Mass Product Formula rep Mass eq prod psi  07d69aa016a2
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Mass Product Formula rep Mass eq prod psi  07d69aa016a2 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Mass Product Formula rep Mass eq prod psi  07d69aa016a2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SumRegroup.lean#L103-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SumRegroup.lean#L103-L154

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLatticeOfFibReps
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumRegroup
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.MassProductFormula
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open UnimodularLocalization GoodPrimeTerms GoodGenusOrbits LocalFactorEquality

theorem P2M_Formalism_HermitianLattices_Ext_L3_MassProductFormula_repMass_eq_prod_psi__07d69aa016a2 (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c) :
    repMass h L (h S.x₀ S.x₀) =
      c * ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, psiP S L 𝔭.1 := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«MassProductFormula».«repMass_eq_prod_psi'» := P2M_Formalism_HermitianLattices_Ext_L3_MassProductFormula_repMass_eq_prod_psi__07d69aa016a2
