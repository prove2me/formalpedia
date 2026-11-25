-- Prove2me | Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_L3_BrB_psiP_eq_sum__9d7549458ff1
-- name    : P2M_Formalism_HermitianLattices_Ext_L3_BrB_psiP_eq_sum__9d7549458ff1
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:56:34.751605+00:00
-- url     : https://prove2.me/theorems/2187a322-0e22-4215-8311-b6ce2f59ed79
-- title:
--   P2 M Formalism Hermitian Lattices Ext L3 Br B psi P eq sum  9d7549458ff1: P2 M Formalism Hermitian Lattices Ext L3 Br B psi P eq sum  9d7549458ff1
-- statement:
--   The P2 M Formalism Hermitian Lattices Ext L3 Br B psi P eq sum  9d7549458ff1 construction uses the P2 M Formalism Hermitian Lattices Ext L3 Br B psi P eq sum  9d7549458ff1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SumLocRepsEq.lean#L103-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SumLocRepsEq.lean#L103-L109

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

theorem P2M_Formalism_HermitianLattices_Ext_L3_BrB_psiP_eq_sum__9d7549458ff1 (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) {s : Finset (Submodule (𝓞 K) V')} (hsr : IsLocReps S L 𝔭 s) :
    psiP S L 𝔭 = ∑ T ∈ s, (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 := by sorry

alias «Formalism».«HermitianLattices».«Ext».«L3».«BrB».«psiP_eq_sum'» := P2M_Formalism_HermitianLattices_Ext_L3_BrB_psiP_eq_sum__9d7549458ff1
