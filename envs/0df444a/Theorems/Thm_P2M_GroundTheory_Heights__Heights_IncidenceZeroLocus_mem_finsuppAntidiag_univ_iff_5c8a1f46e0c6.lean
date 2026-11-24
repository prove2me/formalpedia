-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_mem_finsuppAntidiag_univ_iff_5c8a1f46e0c6
-- name    : P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_mem_finsuppAntidiag_univ_iff_5c8a1f46e0c6
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T01:24:35.868852+00:00
-- url     : https://prove2.me/theorems/f922f1b8-66e9-4d41-b052-5070ed208146
-- title:
--   P2 M Ground Theory Heights  Heights Incidence Zero Locus mem finsupp Antidiag univ iff 5c8a1f46e0c6: P2 M Ground Theory Heights  Heights Incidence Zero Locus mem finsupp Antidiag univ iff 5c8a1f46e0c6
-- statement:
--   The P2 M Ground Theory Heights  Heights Incidence Zero Locus mem finsupp Antidiag univ iff 5c8a1f46e0c6 construction uses the P2 M Ground Theory Heights  Heights Incidence Zero Locus mem finsupp Antidiag univ iff 5c8a1f46e0c6 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PIncidenceZeroLocus.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ArithmeticBezout/PIncidenceZeroLocus.lean#L42-L44

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncidenceZeroLocus
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PIncidenceZeroLocus
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
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IncidenceZeroLocus

theorem P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_mem_finsuppAntidiag_univ_iff_5c8a1f46e0c6 {n N : ℕ} (f : Fin n →₀ ℕ) :
    f ∈ (Finset.univ : Finset (Fin n)).finsuppAntidiag N ↔ f.degree = N := by sorry

alias «GroundTheory».«Heights₂».«Heights».«IncidenceZeroLocus».«mem_finsuppAntidiag_univ_iff» := P2M_GroundTheory_Heights__Heights_IncidenceZeroLocus_mem_finsuppAntidiag_univ_iff_5c8a1f46e0c6
