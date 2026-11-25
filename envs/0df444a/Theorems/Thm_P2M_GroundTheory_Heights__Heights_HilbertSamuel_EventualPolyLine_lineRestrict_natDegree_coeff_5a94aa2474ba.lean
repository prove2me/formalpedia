-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_lineRestrict_natDegree_coeff_5a94aa2474ba
-- name    : P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_lineRestrict_natDegree_coeff_5a94aa2474ba
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:19:06.261988+00:00
-- url     : https://prove2.me/theorems/0b3b32e7-4f1d-4201-a854-2acb93cfaed4
-- title:
--   P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line line Restrict nat Degree coeff 5a94aa2474ba: P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line line Restrict n
-- statement:
--   The P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line line Restrict nat Degree coeff 5a94aa2474ba construction uses the P2 M Ground Theory Heights  Heights Hilbert Samuel Eventual Poly Line line Restrict nat Degree coeff 5a94aa2474ba property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolyLine.lean#L49-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HilbertSamuel/PEventualPolyLine.lean#L49-L73

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

theorem P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_lineRestrict_natDegree_coeff_5a94aa2474ba [Fintype K] (D : ℕ) (a c : K → ℚ) (p : MvPolynomial K ℚ)
    (hp : p.totalDegree ≤ D) :
    (lineRestrict a c p).natDegree ≤ D ∧ (lineRestrict a c p).coeff D = topCoeff D a p := by sorry

alias «GroundTheory».«Heights₂».«Heights».«HilbertSamuel».«EventualPolyLine».«lineRestrict_natDegree_coeff» := P2M_GroundTheory_Heights__Heights_HilbertSamuel_EventualPolyLine_lineRestrict_natDegree_coeff_5a94aa2474ba
