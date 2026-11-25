-- Prove2me | Theorems.Thm_P2M_Formalism_MainNotions_BridgeLemma__fg_of_orthonormal_basis_b96de8b44bc5
-- name    : P2M_Formalism_MainNotions_BridgeLemma__fg_of_orthonormal_basis_b96de8b44bc5
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:59:50.320988+00:00
-- url     : https://prove2.me/theorems/5bd96018-393a-4c0e-b03e-38304383a68a
-- title:
--   P2 M Formalism Main Notions Bridge Lemma  fg of orthonormal basis b96de8b44bc5: P2 M Formalism Main Notions Bridge Lemma  fg of orthonormal basis b96de8b44bc5
-- statement:
--   The P2 M Formalism Main Notions Bridge Lemma  fg of orthonormal basis b96de8b44bc5 construction uses the P2 M Formalism Main Notions Bridge Lemma  fg of orthonormal basis b96de8b44bc5 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/GenusOrthonormalIntegralUnimodular.lean#L28-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/CayleyDegreeNondegeneracy/GenusOrthonormalIntegralUnimodular.lean#L28-L30

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

theorem P2M_Formalism_MainNotions_BridgeLemma__fg_of_orthonormal_basis_b96de8b44bc5 (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) {n : ℕ} (hL : IsOrthoLattice h L n) : L.FG := by sorry

alias «Formalism».«MainNotions».«BridgeLemma₂».«fg_of_orthonormal_basis» := P2M_Formalism_MainNotions_BridgeLemma__fg_of_orthonormal_basis_b96de8b44bc5
