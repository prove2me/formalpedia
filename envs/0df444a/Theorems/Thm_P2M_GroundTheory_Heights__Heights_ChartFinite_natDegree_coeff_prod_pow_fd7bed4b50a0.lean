-- Prove2me | Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartFinite_natDegree_coeff_prod_pow_fd7bed4b50a0
-- name    : P2M_GroundTheory_Heights__Heights_ChartFinite_natDegree_coeff_prod_pow_fd7bed4b50a0
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:35:38.530638+00:00
-- url     : https://prove2.me/theorems/a63d74e0-b476-50a5-a182-51c84cd0e247
-- title:
--   P2 M Ground Theory Heights  Heights Chart Finite nat Degree coeff prod pow fd7bed4b50a0: P2 M Ground Theory Heights  Heights Chart Finite nat Degree coeff prod pow fd7bed4b50a0
-- statement:
--   The P2 M Ground Theory Heights  Heights Chart Finite nat Degree coeff prod pow fd7bed4b50a0 construction uses the P2 M Ground Theory Heights  Heights Chart Finite nat Degree coeff prod pow fd7bed4b50a0 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartFinite.lean#L15-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ChowForms/PChartFinite.lean#L15-L28

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

theorem P2M_GroundTheory_Heights__Heights_ChartFinite_natDegree_coeff_prod_pow_fd7bed4b50a0 {S ι : Type*} [CommRing S] (s : Finset ι) (p : ι → Polynomial S)
    (a k : ι → ℕ) (h : ∀ i ∈ s, (p i).natDegree ≤ a i) :
    (∏ i ∈ s, p i ^ k i).natDegree ≤ ∑ i ∈ s, k i * a i ∧
      (∏ i ∈ s, p i ^ k i).coeff (∑ i ∈ s, k i * a i) = ∏ i ∈ s, (p i).coeff (a i) ^ k i := by sorry

alias «GroundTheory».«Heights₂».«Heights».«ChartFinite».«natDegree_coeff_prod_pow» := P2M_GroundTheory_Heights__Heights_ChartFinite_natDegree_coeff_prod_pow_fd7bed4b50a0
