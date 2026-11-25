-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__finrank_orthonormal_plane_eq_two_4d6f147f5377
-- name    : P2M_Formalism_MainNotions_BridgeLemma__finrank_orthonormal_plane_eq_two_4d6f147f5377
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:00:06.968697+00:00
-- url     : https://prove2.me/theorems/76f32bb9-6d61-418d-84a6-1a9d557bb147
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  finrank orthonormal plane eq two 4d6f147f5377: P2 M Formalism Main Notions Bridge Lemma  finrank orthonormal plane eq two 4d6f147f5377
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  finrank orthonormal plane eq two 4d6f147f5377 construction uses the P2 M Formalism Main Notions Bridge Lemma  finrank orthonormal plane eq two 4d6f147f5377 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L128-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L128-L131

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

theorem P2M_Formalism_MainNotions_BridgeLemma__finrank_orthonormal_plane_eq_two_4d6f147f5377 (L : Submodule (𝓞 K) V) (hL : IsOrthoLattice h L 2) : finrank K V = 2 := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«finrank_orthonormal_plane_eq_two» := P2M_Formalism_MainNotions_BridgeLemma__finrank_orthonormal_plane_eq_two_4d6f147f5377
