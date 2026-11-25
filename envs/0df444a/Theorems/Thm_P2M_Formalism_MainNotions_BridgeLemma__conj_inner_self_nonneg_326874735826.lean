-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__conj_inner_self_nonneg_326874735826
-- name    : P2M_Formalism_MainNotions_BridgeLemma__conj_inner_self_nonneg_326874735826
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:00:10.893021+00:00
-- url     : https://prove2.me/theorems/1a00e37b-ad38-4cc5-85a4-daf968c0dda2
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  conj inner self nonneg 326874735826: P2 M Formalism Main Notions Bridge Lemma  conj inner self nonneg 326874735826
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  conj inner self nonneg 326874735826 construction uses the P2 M Formalism Main Notions Bridge Lemma  conj inner self nonneg 326874735826 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L91-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L91-L103

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_FockGram_FockGramProofs_CovolGram
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_TraceInnerPosOfOrthonormalPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.MainNotions Formalism.MainNotions.BridgeLemma₂
open NumberField Module Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem P2M_Formalism_MainNotions_BridgeLemma__conj_inner_self_nonneg_326874735826 (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V) (hli : LinearIndependent K e)
    (hsp : Submodule.span K (Set.range e) = ⊤) (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x : V)
    (σ : K →ₐ[ℚ] ℂ) : ∃ r : ℝ, 0 ≤ r ∧ σ (h x x) = (r : ℂ) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«conj_inner_self_nonneg» := P2M_Formalism_MainNotions_BridgeLemma__conj_inner_self_nonneg_326874735826
