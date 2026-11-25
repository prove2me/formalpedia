-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFinite_linePoly_natDegree_coeff_9c7308ab0736
-- name    : P2M_GroundTheory_Heights__Heights_ChartFinite_linePoly_natDegree_coeff_9c7308ab0736
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T09:35:18.369921+00:00
-- url     : https://prove2.me/theorems/74211759-36fb-4ad1-8d21-73956604ab00
-- title:
--   P2 M Ground Theory Heights  Heights Chart Finite line Poly nat Degree coeff 9c7308ab0736: P2 M Ground Theory Heights  Heights Chart Finite line Poly nat Degree coeff 9c7308ab0736
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Finite line Poly nat Degree coeff 9c7308ab0736 construction uses the P2 M Ground Theory Heights  Heights Chart Finite line Poly nat Degree coeff 9c7308ab0736 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartFinite.lean#L55-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartFinite.lean#L55-L83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PFGNullstellensatz
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChartFinite
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
open GroundTheory.Heights₂.Heights.ChartFinite
variable {F : Type} [Field F] {n e : ℕ}

theorem P2M_GroundTheory_Heights__Heights_ChartFinite_linePoly_natDegree_coeff_9c7308ab0736 {δ : ℕ} {f : MvPolynomial (Fin (e + 1) × Fin n) F}
    (hf : IsMultiHomog δ f) (t : Fin n → F) (m : Fin n) :
    (linePoly f t m).natDegree ≤ δ ∧ (linePoly f t m).coeff δ = specFirst f t := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartFinite».«linePoly_natDegree_coeff» := P2M_GroundTheory_Heights__Heights_ChartFinite_linePoly_natDegree_coeff_9c7308ab0736
