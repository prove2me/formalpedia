-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_isTransverseSliceAt_iff_4bf6e33116db
-- name    : P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_isTransverseSliceAt_iff_4bf6e33116db
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T04:53:13.003228+00:00
-- url     : https://prove2.me/theorems/15a7349a-6325-5514-801a-2425da8af629
-- title:
--   P2 M Ground Theory Heights  Heights Transverse Slice General is Transverse Slice At iff 4bf6e33116db: P2 M Ground Theory Heights  Heights Transverse Slice General is Transverse Slice At iff 4bf6e33116
-- statement:
--   The P2 M Ground Theory Heights  Heights Transverse Slice General is Transverse Slice At iff 4bf6e33116db construction uses the P2 M Ground Theory Heights  Heights Transverse Slice General is Transverse Slice At iff 4bf6e33116db property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L107-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L107-L135

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTransverseSliceGeneral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_JacMinorC
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsExpansion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTransverseSliceGeneral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix ComplexSets Filter Topology
noncomputable section
open GroundTheory.Heights₂.Heights.TransverseSliceGeneral
variable {n d : ℕ}

theorem P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_isTransverseSliceAt_iff_4bf6e33116db (W : Ideal (MvPolynomial (Fin n) ℂ)) (L : Matrix (Fin d) (Fin n) ℂ)
    (q : Fin n → ℂ) (hq : q ∈ zeroSet W) :
    IsTransverseSliceAt W L q ↔ gradSpace W q ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤ := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TransverseSliceGeneral».«isTransverseSliceAt_iff» := P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_isTransverseSliceAt_iff_4bf6e33116db
