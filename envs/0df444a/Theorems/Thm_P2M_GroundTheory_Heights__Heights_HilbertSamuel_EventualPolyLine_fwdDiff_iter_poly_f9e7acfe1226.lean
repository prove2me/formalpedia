-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_fwdDiff_iter_poly_f9e7acfe1226
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_fwdDiff_iter_poly_f9e7acfe1226
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:21:06.571168+00:00
-- url     : https://prove2.me/theorems/00779dd9-bfa0-5b0b-8421-9b238487db89
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line fwd Diff iter poly f9e7acfe1226: P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line fwd Diff iter poly f9e7acfe
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line fwd Diff iter poly f9e7acfe1226 construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line fwd Diff iter poly f9e7acfe1226 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolyLine.lean#L75-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolyLine.lean#L75-L84

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsEventualPolyLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PEventualValueFacts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PEventualPolyLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open Polynomial GroundTheory.Heights₂.Heights.NumbersDVR fwdDiff
noncomputable section
open GroundTheory.Heights₂.Heights.HilbertSamuel.EventualPolyLine
variable {K : Type}

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_fwdDiff_iter_poly_f9e7acfe1226 (D : ℕ) (P : ℚ[X]) (hP : P.natDegree ≤ D) :
    (fwdDiff (1 : ℚ))^[D] P.eval 0 = (D.factorial : ℚ) * P.coeff D := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«EventualPolyLine».«fwdDiff_iter_poly» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_fwdDiff_iter_poly_f9e7acfe1226
