-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__genus_orthonormal_integral_unimodular_0fe520ecdeca
-- name    : P2M_Formalism_MainNotions_BridgeLemma__genus_orthonormal_integral_unimodular_0fe520ecdeca
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:00:21.284021+00:00
-- url     : https://prove2.me/theorems/71240c21-efc3-4d66-9499-6a4d9d86403c
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  genus orthonormal integral unimodular 0fe520ecdeca: P2 M Formalism Main Notions Bridge Lemma  genus orthonormal integral unimodular 0fe520ecdeca
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  genus orthonormal integral unimodular 0fe520ecdeca construction uses the P2 M Formalism Main Notions Bridge Lemma  genus orthonormal integral unimodular 0fe520ecdeca property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/GenusOrthonormalIntegralUnimodular.lean#L71-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/GenusOrthonormalIntegralUnimodular.lean#L71-L74

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

theorem P2M_Formalism_MainNotions_BridgeLemma__genus_orthonormal_integral_unimodular_0fe520ecdeca (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n)
    (M : Submodule (𝓞 K) V) (hM : M ∈ genus h L) : IsIntegralLat h M ∧ dual h M = M := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«genus_orthonormal_integral_unimodular» := P2M_Formalism_MainNotions_BridgeLemma__genus_orthonormal_integral_unimodular_0fe520ecdeca
