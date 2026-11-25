-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__inner_sum_orthonormal_bc617198dc85
-- name    : P2M_Formalism_MainNotions_BridgeLemma__inner_sum_orthonormal_bc617198dc85
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:01:04.874713+00:00
-- url     : https://prove2.me/theorems/1b0e2386-3903-4ceb-b81b-b47166e7cff7
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  inner sum orthonormal bc617198dc85: P2 M Formalism Main Notions Bridge Lemma  inner sum orthonormal bc617198dc85
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  inner sum orthonormal bc617198dc85 construction uses the P2 M Formalism Main Notions Bridge Lemma  inner sum orthonormal bc617198dc85 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/GenusOrthonormalIntegralUnimodular.lean#L20-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/GenusOrthonormalIntegralUnimodular.lean#L20-L26

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_FinalNeighbourConstruct
import Definitions.Def_Formalism_HermitianLattices_FinalMass
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_GenusOrthonormalIntegralUnimodular
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
open NumberField Formalism.HermitianLatticesTheory
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem P2M_Formalism_MainNotions_BridgeLemma__inner_sum_orthonormal_bc617198dc85 (h : V →ₗ⋆[K] V →ₗ[K] K) {n : ℕ} (e : Fin n → V)
    (he : ∀ i j, h (e i) (e j) = if i = j then 1 else 0) (a b : Fin n → K) :
    h (∑ i, a i • e i) (∑ j, b j • e j) = ∑ i, star (a i) * b i := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«inner_sum_orthonormal» := P2M_Formalism_MainNotions_BridgeLemma__inner_sum_orthonormal_bc617198dc85
