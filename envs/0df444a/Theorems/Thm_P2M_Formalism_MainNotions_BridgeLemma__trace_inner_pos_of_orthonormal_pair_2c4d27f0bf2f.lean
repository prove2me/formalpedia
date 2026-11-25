-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__trace_inner_pos_of_orthonormal_pair_2c4d27f0bf2f
-- name    : P2M_Formalism_MainNotions_BridgeLemma__trace_inner_pos_of_orthonormal_pair_2c4d27f0bf2f
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:59:53.499732+00:00
-- url     : https://prove2.me/theorems/ab6cc001-c8af-49fd-ae23-39addcd31297
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  trace inner pos of orthonormal pair 2c4d27f0bf2f: P2 M Formalism Main Notions Bridge Lemma  trace inner pos of orthonormal pair 2c4d27f0bf2f
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  trace inner pos of orthonormal pair 2c4d27f0bf2f construction uses the P2 M Formalism Main Notions Bridge Lemma  trace inner pos of orthonormal pair 2c4d27f0bf2f property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L105-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/TraceInnerPosOfOrthonormalPair.lean#L105-L138

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

theorem P2M_Formalism_MainNotions_BridgeLemma__trace_inner_pos_of_orthonormal_pair_2c4d27f0bf2f (hK : IsCMUnram K) (h : V →ₗ⋆[K] V →ₗ[K] K) (e : Fin 2 → V) (hli : LinearIndependent K e)
    (hsp : Submodule.span K (Set.range e) = ⊤) (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (x : V)
    (hx : x ≠ 0) : 0 < Algebra.trace ℚ K (h x x) := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«trace_inner_pos_of_orthonormal_pair» := P2M_Formalism_MainNotions_BridgeLemma__trace_inner_pos_of_orthonormal_pair_2c4d27f0bf2f
