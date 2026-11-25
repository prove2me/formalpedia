-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_isOpen_dense_sup_span_rows_093d7c676508
-- name    : P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_isOpen_dense_sup_span_rows_093d7c676508
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T04:42:26.110381+00:00
-- url     : https://prove2.me/theorems/c7c934f2-2d95-4da9-a2e5-cce37c0f97fd
-- title:
--   P2 M Ground Theory Heights  Heights Transverse Slice General is Open dense sup span rows 093d7c676508: P2 M Ground Theory Heights  Heights Transverse Slice General is Open dense sup span rows 093d7c67
-- statement:
--   The P2 M Ground Theory Heights  Heights Transverse Slice General is Open dense sup span rows 093d7c676508 construction uses the P2 M Ground Theory Heights  Heights Transverse Slice General is Open dense sup span rows 093d7c676508 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L174-L241
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PTransverseSliceGeneral.lean#L174-L241

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

theorem P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_isOpen_dense_sup_span_rows_093d7c676508 (V : Submodule ℂ (Fin n → ℂ)) (hV : n ≤ Module.finrank ℂ V + d) :
    IsOpen {L : Matrix (Fin d) (Fin n) ℂ | V ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤} ∧
      Dense {L : Matrix (Fin d) (Fin n) ℂ | V ⊔ Submodule.span ℂ (Set.range fun i => L i) = ⊤} := by sorry

alias «GroundTheory».«Heights₂».«Heights».«TransverseSliceGeneral».«isOpen_dense_sup_span_rows» := P2M_GroundTheory_Heights__Heights_TransverseSliceGeneral_isOpen_dense_sup_span_rows_093d7c676508
