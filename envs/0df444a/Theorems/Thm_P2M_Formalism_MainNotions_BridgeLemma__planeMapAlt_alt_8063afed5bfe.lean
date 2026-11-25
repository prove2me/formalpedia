-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__planeMapAlt_alt_8063afed5bfe
-- name    : P2M_Formalism_MainNotions_BridgeLemma__planeMapAlt_alt_8063afed5bfe
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:01:03.860287+00:00
-- url     : https://prove2.me/theorems/a51517b9-e8e0-4531-87f0-15c906dd13cc
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  plane Map Alt alt 8063afed5bfe: P2 M Formalism Main Notions Bridge Lemma  plane Map Alt alt 8063afed5bfe
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  plane Map Alt alt 8063afed5bfe construction uses the P2 M Formalism Main Notions Bridge Lemma  plane Map Alt alt 8063afed5bfe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L159-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/ProdNormEmbeddingsEqAbsNorm.lean#L159-L166

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

theorem P2M_Formalism_MainNotions_BridgeLemma__planeMapAlt_alt_8063afed5bfe (hs : h.IsSymm) (hfr : finrank K V = 2) (x y x' y' : V) (hxy : h x y = 0) (hxx : h x x ≠ 0)
    (hyy : h y y ≠ 0) (hxy' : h x' y' = 0) (hxx' : h x' x' ≠ 0) (hyy' : h y' y' ≠ 0) (v : V) :
    planeMapAlt h x y x' y' (planeMapAlt h x' y' x y v) = v := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«planeMapAlt_alt» := P2M_Formalism_MainNotions_BridgeLemma__planeMapAlt_alt_8063afed5bfe
