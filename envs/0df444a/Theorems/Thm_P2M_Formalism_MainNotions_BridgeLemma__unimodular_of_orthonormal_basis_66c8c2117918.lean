-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__unimodular_of_orthonormal_basis_66c8c2117918
-- name    : P2M_Formalism_MainNotions_BridgeLemma__unimodular_of_orthonormal_basis_66c8c2117918
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:59:58.062645+00:00
-- url     : https://prove2.me/theorems/91549eea-47ac-498f-92bd-261d552f1d49
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  unimodular of orthonormal basis 66c8c2117918: P2 M Formalism Main Notions Bridge Lemma  unimodular of orthonormal basis 66c8c2117918
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  unimodular of orthonormal basis 66c8c2117918 construction uses the P2 M Formalism Main Notions Bridge Lemma  unimodular of orthonormal basis 66c8c2117918 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/GenusOrthonormalIntegralUnimodular.lean#L48-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/GenusOrthonormalIntegralUnimodular.lean#L48-L69

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

theorem P2M_Formalism_MainNotions_BridgeLemma__unimodular_of_orthonormal_basis_66c8c2117918 (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n) :
    IsUnimodular h L := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«unimodular_of_orthonormal_basis» := P2M_Formalism_MainNotions_BridgeLemma__unimodular_of_orthonormal_basis_66c8c2117918
