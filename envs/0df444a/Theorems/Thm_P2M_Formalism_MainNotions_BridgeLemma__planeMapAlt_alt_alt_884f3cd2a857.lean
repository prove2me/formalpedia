-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__planeMapAlt_alt_alt_884f3cd2a857
-- name    : P2M_Formalism_MainNotions_BridgeLemma__planeMapAlt_alt_alt_884f3cd2a857
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:00:11.112799+00:00
-- url     : https://prove2.me/theorems/d7b5b485-5149-4046-bdff-aa9a880885be
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  plane Map Alt alt alt 884f3cd2a857: P2 M Formalism Main Notions Bridge Lemma  plane Map Alt alt alt 884f3cd2a857
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  plane Map Alt alt alt 884f3cd2a857 construction uses the P2 M Formalism Main Notions Bridge Lemma  plane Map Alt alt alt 884f3cd2a857 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L224-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L224-L227

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ShortVectorEveryPlace
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubgroupsOfIndexLe
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_CayleyDegreeNondegeneracy_ProdNormEmbeddingsEqAbsNorm
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
open NumberField Formalism.HermitianLatticesTheory Module
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  (h : V →ₗ⋆[K] V →ₗ[K] K)

theorem P2M_Formalism_MainNotions_BridgeLemma__planeMapAlt_alt_alt_884f3cd2a857 (hs : h.IsSymm) (x y x' y' : V) (hxy : h x y = 0) (hxx : h x x ≠ 0) :
    planeMapAlt h x y x' y' x = x' := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«planeMapAlt_alt_alt» := P2M_Formalism_MainNotions_BridgeLemma__planeMapAlt_alt_alt_884f3cd2a857
