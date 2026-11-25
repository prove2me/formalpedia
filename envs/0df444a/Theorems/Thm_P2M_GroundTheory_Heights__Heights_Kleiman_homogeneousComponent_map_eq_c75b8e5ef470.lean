-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_map_eq_c75b8e5ef470
-- name    : P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_map_eq_c75b8e5ef470
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:02:02.486346+00:00
-- url     : https://prove2.me/theorems/813598f2-56ca-55b7-aa00-2aaefa0daa44
-- title:
--   P2 M Ground Theory Heights  Heights Kleiman homogeneous Component map eq c75b8e5ef470: P2 M Ground Theory Heights  Heights Kleiman homogeneous Component map eq c75b8e5ef470
-- statement:
--   The P2 M Ground Theory Heights  Heights Kleiman homogeneous Component map eq c75b8e5ef470 construction uses the P2 M Ground Theory Heights  Heights Kleiman homogeneous Component map eq c75b8e5ef470 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreSectionsFlat.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PFibreSectionsFlat.lean#L21-L26

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreSectionsFlat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsGenericRestrLen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsFibreRestrKer
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsRestrQuotTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsDedekindFibreRank
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExtendTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PFibreSectionsFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
open scoped Pointwise
noncomputable section
universe u w

theorem P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_map_eq_c75b8e5ef470 {R R' : Type*} [CommRing R] [CommRing R'] (φ : R →+* R') {N : ℕ}
    (d : ℕ) (p : Poly R N) :
    homogeneousComponent d (MvPolynomial.map φ p) = MvPolynomial.map φ (homogeneousComponent d p) := by sorry

alias «GroundTheory».«Heights₂».«Heights».«Kleiman».«homogeneousComponent_map_eq» := P2M_GroundTheory_Heights__Heights_Kleiman_homogeneousComponent_map_eq_c75b8e5ef470
